import ThesisCommon.Analysis.LpOperatorMatrixDecomposition
import ThesisCommon.Analysis.LpOperatorMatrixRetraction

/-! The actual operator space B(lp) is isomorphic to the bounded product
of its growing finite matrix blocks. Both complementary embeddings and
the required countable self-similarity are constructed in the imports. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

def lpOperatorMatrixEquiv (p : BanachExponent) (hp : 0 < p.val.toReal) :
    ScalarLpOperator 𝕜 p ≃L[𝕜] FiniteMatrixSum 𝕜 p :=
  lpOperatorMatrixEquivOfRetraction p hp (lpOperatorInitialCorners p)
    (matrixProductOperatorLimit p hp) (matrixProductOperatorLimit_comp_initialCorners p hp)

end ThesisCommon
