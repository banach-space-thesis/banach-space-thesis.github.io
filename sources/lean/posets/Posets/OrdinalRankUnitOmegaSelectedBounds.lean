import Posets.OrdinalRankUnitOmegaSelectedEscape

/-! Smaller cells inherit disjointness and the selected cores' cross-mass
bound from their actual outer blocks. -/

noncomputable section
open Set Topology
universe u
namespace Posets

variable {𝕜 : Type*} [RCLike 𝕜] {ρ : Ordinal.{u}} {hρ : Ordinal.omega0 ≤ ρ}
  {M : JLMS.AtomicDualModel 𝕜 (Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))} {N : ℕ} {ε δ : ℝ}

namespace OrdinalRankUnitOmegaColouredCores

variable (F : OrdinalRankUnitOmegaColouredCores ρ hρ M T S N ε δ)
  (H : ℕ → Set (Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0)))
  (hH : ∀ i, H i ⊆ range (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (F.index i)))

include F hH

theorem selected_disjoint : Pairwise (fun i j => Disjoint (H i) (H j)) := by
  intro i j hij
  have hd := ordinalRankUnitOmegaOuterFamily_disjoint ρ hρ
    (ordinalRankUnitOmegaOuterHeight N) (ordinalRankUnitOmegaOuterHeight_strictMono N)
    (F.strictMono.injective.ne hij)
  exact hd.mono (hH i) (hH j)

theorem selected_cross_subset (i : ℕ) :
    wolfeCrossUnion H i ⊆ wolfeCrossUnion
      (fun j => range (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (F.index j))) i := by
  intro x hx
  obtain ⟨j, hji, hxj⟩ := (mem_wolfeCrossUnion H i x).mp hx
  exact (mem_wolfeCrossUnion _ i x).mpr ⟨j, hji, hH j hxj⟩

theorem selected_cross_bound (i : ℕ) (x : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))
    (hx : x ∈ F.core i) :
    ‖JLMS.atomicRestriction M (wolfeCrossUnion H i)
      ((JLMS.evaluation x).comp (if F.colour then T else S))‖ ≤ δ := by
  exact ((wolfeMass_mono M (wolfeOperatorRow (if F.colour then T else S) x)
    (F.selected_cross_subset H hH i)).trans_lt (F.cross i x hx)).le

end OrdinalRankUnitOmegaColouredCores
end Posets


