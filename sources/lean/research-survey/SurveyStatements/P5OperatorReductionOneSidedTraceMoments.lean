import SurveyStatements.P5OperatorReductionOneSidedMoments
import SurveyStatements.P5OperatorReductionVarianceLimits

/-! Uniform primal-side moments pass to actual scalar trace limits. No
vector-valued limiting operator is assumed or constructed. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem limiting_functional_signedBlock_second_moment_le_uniform
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ)
    (S : Finset (Fin (2 ^ n)))
    (φ : ℕ → IntervalLp 𝕜 p →L[𝕜] 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (hφ : ∀ m, ‖φ m‖ ≤ C)
    (a : (Fin (2 ^ n) → Bool) → 𝕜)
    (ha : ∀ θ, Tendsto (fun m => φ m (lpHaarSignedBlock 𝕜 p n S θ))
      atTop (𝓝 (a θ))) :
    mean (fun θ => ‖a θ‖ ^ 2) ≤
      C ^ 2 * intervalLpDyadicRadius n ^ (1 / p.val.toReal) :=
  signed_second_moment_bound_of_limit _ a ha (Eventually.of_forall (fun m =>
    functional_signedBlock_second_moment_le_uniform p hp (φ m) hC (hφ m) n S))

theorem limiting_functional_signedBlock_second_moment_tendsto_zero
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (S : ∀ n, Finset (Fin (2 ^ n)))
    (φ : ℕ → ℕ → IntervalLp 𝕜 p →L[𝕜] 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (hφ : ∀ n m, ‖φ n m‖ ≤ C)
    (a : (n : ℕ) → (Fin (2 ^ n) → Bool) → 𝕜)
    (ha : ∀ n θ, Tendsto (fun m => φ n m (lpHaarSignedBlock 𝕜 p n (S n) θ))
      atTop (𝓝 (a n θ))) :
    Tendsto (fun n => mean (fun θ => ‖a n θ‖ ^ 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => C ^ 2 *
      intervalLpDyadicRadius n ^ (1 / p.val.toReal)) atTop (𝓝 0) := by
    simpa using (lpHaarDyadic_norm_radius_tendsto_zero p hp).const_mul (C ^ 2)
  exact squeeze_zero (fun _ => mean_nonneg (fun _ => sq_nonneg _))
    (fun n => limiting_functional_signedBlock_second_moment_le_uniform p hp n
      (S n) (φ n) hC (hφ n) (a n) (ha n)) ht

end SurveyStatements.P5OperatorReduction
