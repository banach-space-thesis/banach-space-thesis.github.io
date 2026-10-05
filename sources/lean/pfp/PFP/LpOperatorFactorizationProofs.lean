import PFP.MatrixSumFactorizationProofs
import ThesisCommon.Analysis.LpOperatorMatrixIsomorphism
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! Full Theorem 5.15, using the actual operator/matrix-product isomorphism
and the checked isomorphic invariance of uniform primary factorisation. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

theorem theorem_5_15 : Theorem_5_15 𝕜 := by
  intro p hp hfin
  have hp0 : 0 < p.val.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp)) hfin
  have hM : HasUPFP 𝕜 (MatrixSum 𝕜 p) := ⟨8, by norm_num, theorem_5_14 (𝕜 := 𝕜) p hp hfin⟩
  exact hM.of_equiv (lpOperatorMatrixEquiv (𝕜 := 𝕜) p hp0).symm

end PFP
