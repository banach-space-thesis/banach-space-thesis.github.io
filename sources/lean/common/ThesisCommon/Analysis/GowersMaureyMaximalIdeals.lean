import ThesisCommon.Analysis.GowersMaureyStrictlySingularCorrections
import ThesisCommon.Analysis.GowersMaureyFiniteRankIdeals

/-! Every algebraically maximal two-sided operator ideal contains all
genuinely strictly singular operators. Finite-rank corrections provide
actual units in the contradiction; no closedness of the maximal ideal
and no finite-spread approximation input is required. -/
noncomputable section
namespace ThesisCommon

theorem twoSidedIdeal_le_isCoatom_of_unit_corrections
    {R : Type*} [Ring R] (I J : TwoSidedIdeal R) (hJ : IsCoatom J)
    (hc : ∀ s ∈ I, ∃ k ∈ J, IsUnit (1-s+k)) : I ≤ J := by
  have hne : J ⊔ I ≠ ⊤ := by
    intro he
    have hmem : (1 : R) ∈ J ⊔ I := he ▸ trivial
    obtain ⟨j,hj,s,hs,hjs⟩ := TwoSidedIdeal.mem_sup.mp hmem
    obtain ⟨k,hk,hu⟩ := hc s hs
    have hunit : 1-s+k ∈ J := by
      have hh : 1-s = j := by rw [← hjs,add_sub_cancel_right]
      rw [hh]
      exact J.add_mem hj hk
    have hone : (1 : R) ∈ J := by
      have hh := J.mul_mem_left (↑hu.unit⁻¹ : R) (1-s+k) hunit
      simpa only [hu.val_inv_mul] using hh
    exact hJ.1 ((TwoSidedIdeal.one_mem_iff J).mp hone)
  exact le_sup_right.trans ((isCoatom_iff_ge_of_le.mp hJ).2 (J ⊔ I) hne le_sup_left)

namespace GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem strictlySingularIdeal_le_maximalOperatorIdeal (D : ConstructionData 𝕜)
    (J : TwoSidedIdeal (ShiftSpace D →L[𝕜] ShiftSpace D)) (hJ : IsCoatom J) :
    strictlySingularIdeal D ≤ J := by
  apply twoSidedIdeal_le_isCoatom_of_unit_corrections (strictlySingularIdeal D) J hJ
  intro S hS
  have hSS := (mem_strictlySingularIdeal D S).mp hS
  obtain ⟨K,hK,hunit⟩ := strictlySingular_hasFiniteRankInvertibleCorrection_id_sub D S hSS
  letI := hK
  exact ⟨K,finiteRank_mem_maximalOperatorIdeal D J hJ K,hunit⟩

theorem allMaximalIdealsContainStrictlySingular (D : ConstructionData 𝕜) :
    AllMaximalIdealsContainStrictlySingular 𝕜 (ShiftSpace D) := by
  intro J hJ T hT
  exact strictlySingularIdeal_le_maximalOperatorIdeal D J hJ
    ((mem_strictlySingularIdeal D T).mpr hT)

end GowersMaurey
end ThesisCommon
