import PFP.BanachMazurStatements
import ThesisCommon.Analysis.BanachMazurApproximateBounds

/-! The justified infimum formulation accompanying Definition 2.1. The
printed endpoint-attainment target is preserved separately and remains open. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type u) (Y : Type v)
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem definition_2_1_approximate_bound {C : ℝ} (hC : 1 ≤ C) :
    Definition_2_1_distance 𝕜 X Y ≤ ENNReal.ofReal C ↔
      ∀ ε : ℝ, 0 < ε → IsomorphicWithBound 𝕜 X Y (C + ε) :=
  banachMazurDistance_le_iff_approximate_isomorphic_bound 𝕜 X Y
    (zero_le_one.trans hC)

end PFP
