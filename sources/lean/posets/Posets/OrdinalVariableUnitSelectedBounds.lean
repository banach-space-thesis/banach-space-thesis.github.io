import Posets.OrdinalVariableUnitSelectedEscape

/-! Smaller cells inherit disjointness and the selected cores' cross-mass
bound from their actual outer blocks. -/

noncomputable section
open Set Topology
universe u
namespace Posets

variable {𝕜 : Type*} [RCLike 𝕜] {γ : Ordinal.{u}} {N : ℕ} {P : OrdinalVariableUnitParameters γ N}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ))}
  {T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))} {ε δ : ℝ}

namespace OrdinalVariableUnitColouredCores

variable (F : OrdinalVariableUnitColouredCores P M T S ε δ)
  (H : ℕ → Set (Iio (Ordinal.omega0 ^ γ)))
  (hH : ∀ i, H i ⊆ range (P.embedding (F.index i)))

include F hH

theorem selected_disjoint : Pairwise (fun i j => Disjoint (H i) (H j)) := by
  intro i j hij
  have hd := P.outerBlock_disjoint (F.strictMono.injective.ne hij)
  exact hd.mono (hH i) (hH j)

theorem selected_cross_subset (i : ℕ) :
    wolfeCrossUnion H i ⊆ wolfeCrossUnion
      (fun j => range (P.embedding (F.index j))) i := by
  intro x hx
  obtain ⟨j, hji, hxj⟩ := (mem_wolfeCrossUnion H i x).mp hx
  exact (mem_wolfeCrossUnion _ i x).mpr ⟨j, hji, hH j hxj⟩

theorem selected_cross_bound (i : ℕ) (x : Iio (Ordinal.omega0 ^ γ))
    (hx : x ∈ F.core i) :
    ‖JLMS.atomicRestriction M (wolfeCrossUnion H i)
      ((JLMS.evaluation x).comp (if F.colour then T else S))‖ ≤ δ := by
  exact ((wolfeMass_mono M (wolfeOperatorRow (if F.colour then T else S) x)
    (F.selected_cross_subset H hH i)).trans_lt (F.cross i x hx)).le

end OrdinalVariableUnitColouredCores
end Posets




