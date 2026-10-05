import UPFP.EllOnePreservation
import ThesisCommon.Analysis.DualCotypePreservation
import ThesisCommon.Analysis.DualCotypeTriangular

/-! The complete Theorem 1.1, including both its self-similarity and
dual-cotype alternatives. The forward input in the latter is proved directly
by the adjoint finite-sign argument; see the recorded proof-method note. -/
namespace UPFP
open ThesisCommon

alias lemma_4_1 := ThesisCommon.HasRademacherCotype.dual_ellOne_backward_reduction
alias proposition_5_1 := ThesisCommon.HasFiniteCotype.dual_ellOne_diagonal_reduction
alias proposition_3_1 := ThesisCommon.HasFiniteCotype.dual_ellOne_upper_triangular
alias proposition_4_3 := ThesisCommon.HasFiniteCotype.dual_ellOne_lower_triangular

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem theorem_1_1_dualFiniteCotype (hX : HasUPFP 𝕜 X)
    (hcotype : HasFiniteCotype (X →L[𝕜] 𝕜)) :
    HasUPFP 𝕜 (EllOneSum ℕ X) ∧ IsPrimary 𝕜 (EllOneSum ℕ X) := by
  have h := hX.ellOne_of_dualFiniteCotype hcotype
  exact ⟨h, h.lp_isPrimary⟩

/-- The full original Theorem 1.1, with no auxiliary analytic assumptions. -/
theorem theorem_1_1_proof : Theorem_1_1 𝕜 X := by
  intro hX h
  rcases h with hself | hcotype
  · exact theorem_1_1_selfSimilar hX hself
  · exact theorem_1_1_dualFiniteCotype hX hcotype

end UPFP
