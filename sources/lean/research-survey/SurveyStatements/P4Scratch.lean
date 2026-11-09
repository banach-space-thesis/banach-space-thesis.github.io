import SurveyStatements.P4DFJPGauge
import SurveyStatements.P4Gantmacher
noncomputable section
set_option autoImplicit false
namespace SurveyStatements.P4
universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
set_option pp.all true in
example (z : StrongDual 𝕜 (StrongDual 𝕜 E)) : dist z 0 = ‖z‖ := by
  exact dist_zero_right z
example (z : StrongDual 𝕜 (StrongDual 𝕜 E)) (b : ℝ) :
    z ∈ Metric.closedBall 0 b ↔ ‖z‖ ≤ b := by
  exact Metric.mem_closedBall_zero_iff
end SurveyStatements.P4
