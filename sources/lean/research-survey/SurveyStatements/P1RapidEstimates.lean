import SurveyStatements.P1Transfer

/-!
The quantitative backward-recursion estimates in the rapid flat-block
alternative, corresponding to `upper-z`, `lower-z`, and `z-error-target`.
-/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The normalized cover estimate tolerates the two normalization errors. -/
theorem rapid_backward_upper {d z : X} (hd : d ≠ 0) (hz : z ≠ 0)
    {θ : ℂ} (hθ : θ ∈ unitScalars) {η ρ : ℝ}
    (hdnorm : |‖d‖ - 1| ≤ η) (hznorm : |‖z‖ - 1| ≤ ρ)
    (hcover : ‖unitNormalize d - θ • unitNormalize z‖ ≤ 1 + η) :
    ‖d - θ • z‖ ≤ 1 + 2 * η + ρ := by
  have hp := phase_norm_perturbation d z (unitNormalize d) (unitNormalize z) hθ
  have hdErr : ‖d - unitNormalize d‖ ≤ η := by
    rw [norm_sub_rev, norm_unitNormalize_sub_self hd, abs_sub_comm]
    exact hdnorm
  have hzErr : ‖z - unitNormalize z‖ ≤ ρ := by
    rw [norm_sub_rev, norm_unitNormalize_sub_self hz, abs_sub_comm]
    exact hznorm
  linarith

/-- The tail projection bound gives the required lower recursion estimate. -/
theorem rapid_backward_lower {d z : X} {θ : ℂ} {η γ : ℝ}
    (hη : 0 ≤ η) (hγ : 0 ≤ γ) (hdnorm : |‖d‖ - 1| ≤ η)
    (hprojection : ‖d‖ ≤ (1 + γ) * ‖d - θ • z‖) :
    1 - η - γ ≤ ‖d - θ • z‖ := by
  have hlower : 1 - η ≤ ‖d‖ := by linarith [(abs_le.mp hdnorm).1]
  have hmult : (1 + γ) * (1 - η - γ) ≤ 1 - η := by
    nlinarith
  nlinarith

/-- Combining both estimates closes one stage of the source's error induction. -/
theorem rapid_backward_error {d z : X} (hd : d ≠ 0) (hz : z ≠ 0)
    {θ : ℂ} (hθ : θ ∈ unitScalars) {η γ ρ : ℝ}
    (hη : 0 ≤ η) (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ)
    (hdnorm : |‖d‖ - 1| ≤ η) (hznorm : |‖z‖ - 1| ≤ ρ)
    (hcover : ‖unitNormalize d - θ • unitNormalize z‖ ≤ 1 + η)
    (hprojection : ‖d‖ ≤ (1 + γ) * ‖d - θ • z‖) :
    |‖d - θ • z‖ - 1| ≤ 2 * η + γ + ρ := by
  apply abs_le.mpr
  have hu := rapid_backward_upper hd hz hθ hdnorm hznorm hcover
  have hl := rapid_backward_lower hη hγ hdnorm hprojection
  constructor <;> linarith

end SurveyStatements.P1
