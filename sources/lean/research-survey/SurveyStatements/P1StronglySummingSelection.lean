import SurveyStatements.P1SuccessivePairs
import SurveyStatements.P1WeakNullSelection

/-! Select asymptotically monotone normalized differences of a nonconvergent
weak-Cauchy sequence while retaining the successive paired indices. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem weakCauchy_nonconvergent_asymptoticallyMonotone_pairs
    {s : ℕ → X} (hs : IsWeakCauchySequence s)
    (hnot : ¬ ∃ x : X, ∀ f : X →L[ℂ] ℂ,
      Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    ∃ r : ℝ, 0 < r ∧ ∃ p q : ℕ → ℕ,
      (∀ n, p n < q n ∧ q n < p (n + 1)) ∧
      (∀ n, r ≤ ‖s (p n) - s (q n)‖) ∧
      IsAsymptoticallyMonotone (fun n => unitNormalize (s (p n) - s (q n))) ∧
      ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
        (1 / 2 : ℝ) *
            ‖sequencePartialSum (fun n => unitNormalize (s (p n) - s (q n))) a N‖ ≤
          ‖sequencePartialSum (fun n => unitNormalize (s (p n) - s (q n))) a M‖ := by
  obtain ⟨r, hr, p, q, hpq, hsep, hnorm, hweak⟩ :=
    weakCauchy_nonconvergent_normalized_successive_pairs hs hnot
  obtain ⟨ν, hν, ham, hp⟩ :=
    weakNull_exists_asymptoticallyMonotone_subsequence_with_bound
      (fun n => unitNormalize (s (p n) - s (q n))) hnorm hweak
  exact ⟨r, hr, p ∘ ν, q ∘ ν, successivePairs_subsequence hpq hν,
    fun n => hsep (ν n), ham, hp⟩

end SurveyStatements.P1
