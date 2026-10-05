import Posets.OrdinalRegularOmegaSelectedEscape

/-! Smaller cells inherit disjointness and the selected cores' cross-mass
bound from their actual outer blocks. -/

noncomputable section
open Set Topology
universe u
namespace Posets

variable {𝕜 : Type*} [RCLike 𝕜] {c : Cardinal.{u}} {hc : Cardinal.aleph0 < c}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (c.ord ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))} {N : ℕ} {ε δ : ℝ}

namespace OrdinalRegularOmegaColouredCores

variable (F : OrdinalRegularOmegaColouredCores c hc M T S N ε δ)
  (H : ℕ → Set (Iio (c.ord ^ Ordinal.omega0)))
  (hH : ∀ i, H i ⊆ range (ordinalRegularOmegaSourceEmbedding c hc N (F.index i)))

include F hH

theorem selected_disjoint : Pairwise (fun i j => Disjoint (H i) (H j)) := by
  intro i j hij
  have hd := ordinalRegularOmegaOuterFamily_disjoint c hc.le
    (ordinalRegularOmegaOuterHeight N) (ordinalRegularOmegaOuterHeight_strictMono N)
    (F.strictMono.injective.ne hij)
  exact hd.mono (hH i) (hH j)

theorem selected_cross_subset (i : ℕ) :
    wolfeCrossUnion H i ⊆ wolfeCrossUnion
      (fun j => range (ordinalRegularOmegaSourceEmbedding c hc N (F.index j))) i := by
  intro x hx
  obtain ⟨j, hji, hxj⟩ := (mem_wolfeCrossUnion H i x).mp hx
  exact (mem_wolfeCrossUnion _ i x).mpr ⟨j, hji, hH j hxj⟩

theorem selected_cross_bound (i : ℕ) (x : Iio (c.ord ^ Ordinal.omega0))
    (hx : x ∈ F.core i) :
    ‖JLMS.atomicRestriction M (wolfeCrossUnion H i)
      ((JLMS.evaluation x).comp (if F.colour then T else S))‖ ≤ δ := by
  exact ((wolfeMass_mono M (wolfeOperatorRow (if F.colour then T else S) x)
    (F.selected_cross_subset H hH i)).trans_lt (F.cross i x hx)).le

end OrdinalRegularOmegaColouredCores
end Posets
