import SurveyStatements.P5OperatorReductionRegisteredTraces
import SurveyStatements.P5OperatorReductionMoments

/-! One actual finite sign choice satisfies all finite errors along an
infinite further reservoir. Newly registered operator traces are then
extracted without losing these errors or any previously registered limit. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped ENNReal BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_fixed_sign_finite_errors_reservoir {m n : ℕ}
    (r : ℕ → ℕ) (hr : StrictMono r)
    (f : Fin m → (Fin n → Bool) → ℕ → 𝕜) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ᶠ k in atTop,
      (∑ i, mean (fun θ : Fin n → Bool => ‖f i θ (r k)‖ ^ 2)) < ε ^ 2) :
    ∃ θ : Fin n → Bool, ∃ s : ℕ → ℕ, StrictMono s ∧
      StrictMono (r ∘ s) ∧ ∀ k i, ‖f i θ (r (s k))‖ < ε := by
  have hgood : ∀ᶠ k in atTop, ∃ θ : Fin n → Bool,
      ∀ i, ‖f i θ (r k)‖ < ε := hsmall.mono (fun k hk =>
    finite_sign_simultaneous_small (fun i θ => f i θ (r k)) hε hk)
  obtain ⟨θ, s, hs, hrs, _, _, hsgood⟩ :=
    exists_fixed_good_reservoir r hr (fun θ l => ∀ i, ‖f i θ l‖ < ε) hgood
  exact ⟨θ, s, hs, hrs, hsgood⟩

theorem exists_fixed_sign_errors_and_registered_traces {m n : ℕ}
    {I : Type*} [Countable I]
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (f : Fin m → (Fin n → Bool) → ℕ → 𝕜) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ᶠ k in atTop,
      (∑ i, mean (fun θ : Fin n → Bool => ‖f i θ (r k)‖ ^ 2)) < ε ^ 2)
    (Q : (Fin n → Bool) → I → IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    {C : ℝ} (hC : 0 ≤ C) (hQ : ∀ θ i, ‖Q θ i‖ ≤ C) :
    ∃ θ : Fin n → Bool, ∃ s : ℕ → ℕ, StrictMono s ∧
      StrictMono (r ∘ s) ∧ (∀ k i, ‖f i θ (r (s k))‖ < ε) ∧
      Nonempty (∀ i, RegisteredDyadicTrace
        (fun l k => lpHaarDyadicCoefficient 𝕜 p l k
          (Q θ i (lpHaarDyadic 𝕜 p l k))) (r ∘ s) (6 * C)) := by
  obtain ⟨θ, s, hs, hrs, herrors⟩ :=
    exists_fixed_sign_finite_errors_reservoir r hr f hε hsmall
  obtain ⟨t, ht, hrst, ⟨a⟩⟩ :=
    exists_registered_operator_traces p hp (Q θ) hC (hQ θ) (r ∘ s) hrs
  refine ⟨θ, s ∘ t, hs.comp ht, ?_, ?_, ?_⟩
  · simpa only [Function.comp_assoc] using hrst
  · intro k i
    exact herrors (t k) i
  · exact ⟨fun i => by simpa only [Function.comp_assoc] using a i⟩

end SurveyStatements.P5OperatorReduction
