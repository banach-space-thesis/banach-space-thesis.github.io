import SurveyStatements.P1StronglySummingPreparation

/-! Successive separated pairs retain their order under subsequences. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

theorem successivePairs_strictMono {p q : ℕ → ℕ}
    (hpair : ∀ n, p n < q n ∧ q n < p (n + 1)) :
    StrictMono p ∧ StrictMono q := by
  constructor
  · exact strictMono_nat_of_lt_succ fun n => (hpair n).1.trans (hpair n).2
  · exact strictMono_nat_of_lt_succ fun n => (hpair n).2.trans (hpair (n + 1)).1

theorem successivePairs_subsequence {p q : ℕ → ℕ}
    (hpair : ∀ n, p n < q n ∧ q n < p (n + 1))
    {ν : ℕ → ℕ} (hν : StrictMono ν) :
    ∀ n, (p ∘ ν) n < (q ∘ ν) n ∧ (q ∘ ν) n < (p ∘ ν) (n + 1) := by
  intro n
  refine ⟨(hpair (ν n)).1, ?_⟩
  have hnext : ν n + 1 ≤ ν (n + 1) := by
    have hn : ν n < ν (n + 1) := hν (by omega)
    omega
  exact (hpair (ν n)).2.trans_le ((successivePairs_strictMono hpair).1.monotone hnext)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The genuine normalization-and-selection input to the strongly summing
case: a weak-Cauchy sequence that is not weakly convergent supplies successive
normalized weakly null differences. -/
theorem weakCauchy_nonconvergent_normalized_successive_pairs [CompleteSpace X]
    {s : ℕ → X} (hs : IsWeakCauchySequence s)
    (hnot : ¬ ∃ x : X, ∀ f : X →L[ℂ] ℂ,
      Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    ∃ r : ℝ, 0 < r ∧ ∃ p q : ℕ → ℕ,
      (∀ n, p n < q n ∧ q n < p (n + 1)) ∧
      (∀ n, r ≤ ‖s (p n) - s (q n)‖) ∧
      (∀ n, ‖unitNormalize (s (p n) - s (q n))‖ = 1) ∧
      ∀ f : X →L[ℂ] ℂ,
        Tendsto (fun n => f (unitNormalize (s (p n) - s (q n)))) atTop (𝓝 0) := by
  have hnc : ¬ CauchySeq s := fun h => hnot (cauchySeq_weakly_convergent h)
  obtain ⟨r, hr, p, q, hpq, hsep⟩ := noncauchy_successive_pairs hnc
  have hmono := successivePairs_strictMono hpq
  exact ⟨r, hr, p, q, hpq, hsep, weakCauchy_unitDifferences_norm hr hsep,
    weakCauchy_unitDifferences_tendsto_zero hs hmono.1.tendsto_atTop
      hmono.2.tendsto_atTop hr hsep⟩

end SurveyStatements.P1
