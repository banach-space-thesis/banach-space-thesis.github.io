import SurveyStatements.P5OperatorReductionMoments
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Finite sign averages commute with actual scalar coefficient limits.
This transfers bounds on the genuine finite averaged operators to their
trace coefficients, without a vector-valued compactness assumption. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support.Grothendieck

theorem mean_tendsto_of_pointwise {Ω : Type*} [Fintype Ω]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (h : ∀ θ, Tendsto (fun m => f m θ) atTop (𝓝 (g θ))) :
    Tendsto (fun m => mean (f m)) atTop (𝓝 (mean g)) := by
  unfold mean
  exact tendsto_const_nhds.mul (tendsto_finset_sum _ (fun θ _ => h θ))

theorem signed_second_moment_tendsto {𝕜 Ω : Type*} [RCLike 𝕜] [Fintype Ω]
    (f : ℕ → Ω → 𝕜) (g : Ω → 𝕜)
    (h : ∀ θ, Tendsto (fun m => f m θ) atTop (𝓝 (g θ))) :
    Tendsto (fun m => mean (fun θ => ‖f m θ‖ ^ 2)) atTop
      (𝓝 (mean (fun θ => ‖g θ‖ ^ 2))) :=
  mean_tendsto_of_pointwise _ _ (fun θ => (h θ).norm.pow 2)

theorem signed_second_moment_bound_of_limit {𝕜 Ω : Type*}
    [RCLike 𝕜] [Fintype Ω] (f : ℕ → Ω → 𝕜) (g : Ω → 𝕜)
    (h : ∀ θ, Tendsto (fun m => f m θ) atTop (𝓝 (g θ))) {C : ℝ}
    (hb : ∀ᶠ m in atTop, mean (fun θ => ‖f m θ‖ ^ 2) ≤ C) :
    mean (fun θ => ‖g θ‖ ^ 2) ≤ C := by
  exact le_of_tendsto (signed_second_moment_tendsto f g h) hb

end SurveyStatements.P5OperatorReduction
