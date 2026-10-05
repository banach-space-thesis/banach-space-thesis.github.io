import ThesisCommon.Analysis.LpOperatorBlocks
import ThesisCommon.Analysis.ComplementedSequenceDecomposition

/-! The countable bounded-product self-similarity of B(lp), obtained by
the checked decomposition method from actual block-diagonal retractions. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (p : BanachExponent) (hp : 0 < p.val.toReal)
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def lpOperatorSequenceEquiv :
    ScalarLpOperator 𝕜 p ≃L[𝕜] lp (fun _ : ℕ => ScalarLpOperator 𝕜 p) ∞ :=
  infinitySequenceEquivOfRetraction (lpOperatorBlockInsert p hp) (lpOperatorBlockRead p hp)
    (lpOperatorBlockRead_comp_insert p hp)

end ThesisCommon
