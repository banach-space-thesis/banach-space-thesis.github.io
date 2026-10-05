import ThesisCommon.Analysis.LpOperatorSelfSimilarity
import ThesisCommon.Analysis.MatrixOperatorBlocks

/-! Pełczyński decomposition for the actual lp operator space and matrix
product. The reverse retraction will be supplied by the finite-corner limit. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

def lpOperatorMatrixEquivOfRetraction (p : BanachExponent) (hp : 0 < p.val.toReal)
    (J : ScalarLpOperator 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p)
    (Q : FiniteMatrixSum 𝕜 p →L[𝕜] ScalarLpOperator 𝕜 p)
    (hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 (ScalarLpOperator 𝕜 p)) :
    ScalarLpOperator 𝕜 p ≃L[𝕜] FiniteMatrixSum 𝕜 p :=
  lpDecompositionEquivOfRetractions ∞ (lpOperatorSequenceEquiv p hp)
    (matrixLpOperatorInsert p hp) (matrixLpOperatorRead p hp)
    (matrixLpOperatorRead_comp_insert p hp) J Q hQJ

end ThesisCommon
