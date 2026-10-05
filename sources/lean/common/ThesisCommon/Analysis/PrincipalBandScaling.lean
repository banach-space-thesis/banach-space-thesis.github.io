import ThesisCommon.Analysis.ALRefinementPrincipal

/-! Nonzero scalar multiples generate the same actual principal band. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
  [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem latticeDisjointComplement_singleton_smul (e : E) (c : ℝ) (hc : c ≠ 0) :
    latticeDisjointComplement ({c • e} : Set E) = latticeDisjointComplement {e} := by
  ext x
  have hs : c • e ∈ latticeDisjointComplement ({x} : Set E) ↔
      e ∈ latticeDisjointComplement ({x} : Set E) := by
    constructor
    · intro h
      simpa only [inv_smul_smul₀ hc] using (latticeDisjointComplement ({x} : Set E)).smul_mem c⁻¹ h
    · intro h
      exact (latticeDisjointComplement ({x} : Set E)).smul_mem c h
  simpa only [mem_latticeDisjointComplement, Set.mem_singleton_iff, forall_eq, inf_comm] using hs

theorem principalBand_smul_of_ne_zero (e : E) (c : ℝ) (hc : c ≠ 0) :
    principalBand (c • e) = principalBand e := by
  simp only [principalBand, latticeDisjointComplement_singleton_smul e c hc]

theorem principalBand_norm_inv_smul (e : E) (he : e ≠ 0) :
    principalBand (‖e‖⁻¹ • e) = principalBand e :=
  principalBand_smul_of_ne_zero e _ (inv_ne_zero (norm_ne_zero_iff.mpr he))

end ThesisCommon
