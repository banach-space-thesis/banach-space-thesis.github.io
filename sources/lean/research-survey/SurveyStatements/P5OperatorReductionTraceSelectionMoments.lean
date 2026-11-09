import SurveyStatements.P5OperatorReductionRegisteredTraces
import SurveyStatements.P5OperatorReductionTraceMoments
import SurveyStatements.P5Support.LpHaarContinuousApproximation

/-! Genuine trace-balance moments and deterministic trace errors can be
combined before the actual common finite sign choice. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem signed_second_moment_add_deterministic_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
    (f : (n : ℕ) → Ω n → 𝕜) (b : ℕ → 𝕜)
    (hf : Tendsto (fun n => mean (fun θ => ‖f n θ‖ ^ 2)) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => mean (fun θ => ‖f n θ + b n‖ ^ 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => 2 * mean (fun θ => ‖f n θ‖ ^ 2) + 2 * ‖b n‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using (hf.const_mul 2).add ((hb.norm.pow 2).const_mul 2)
  apply squeeze_zero (fun n => mean_nonneg (fun _ => sq_nonneg _)) _ ht
  intro n
  calc
    _ ≤ mean (fun θ => 2 * (‖f n θ‖ ^ 2 + ‖b n‖ ^ 2)) :=
      mean_mono (fun θ => norm_add_square_le (f n θ) (b n))
    _ = _ := by rw [mean_mul_left, mean_add, mean_const]; ring

theorem signed_second_moment_const_mul_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
    (f : (n : ℕ) → Ω n → 𝕜) (c : 𝕜)
    (hf : Tendsto (fun n => mean (fun θ => ‖f n θ‖ ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun n => mean (fun θ => ‖c * f n θ‖ ^ 2)) atTop (𝓝 0) := by
  simpa only [norm_mul, mul_pow, mean_mul_left, mul_zero] using hf.const_mul (‖c‖ ^ 2)

theorem registered_trace_split_moment_tendsto_zero
    {d : ∀ n, Fin (2 ^ n) → 𝕜} {r : ℕ → ℕ} {M : ℝ}
    (a : RegisteredDyadicTrace d r M) (hM : 0 ≤ M)
    (S : ∀ n, Finset (Fin (2 ^ n))) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖a.value ⟨n + 1, lpHaarSignedChildAtoms n (S n) θ⟩ -
        (2 : 𝕜)⁻¹ * a.value ⟨n, S n⟩‖ ^ 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => M ^ 2 * intervalLpDyadicRadius n / 4)
      atTop (𝓝 0) := by
    simpa using (lpHaarDyadicRadius_tendsto.const_mul (M ^ 2)).div_const 4
  exact squeeze_zero (fun _ => mean_nonneg (fun _ => sq_nonneg _))
    (fun n => lpHaarTrace_split_second_moment_le a.value a.additive hM a.bound n (S n)) ht

end SurveyStatements.P5OperatorReduction
