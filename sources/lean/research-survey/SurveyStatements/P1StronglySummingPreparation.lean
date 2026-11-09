import SurveyStatements.P1WeakDifferences
import SurveyStatements.P1UniformBoundedness
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.MetricSpace.Cauchy

/-!
The boundedness and separated successive-pair prerequisites for the
strongly summing branch.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Weak Cauchyness implies uniform norm boundedness by Banach--Steinhaus
on the actual complex dual. -/
theorem weakCauchy_norm_bounded {s : ℕ → X} (hs : IsWeakCauchySequence s) :
    ∃ M : ℝ, ∀ n, ‖s n‖ ≤ M := by
  let g : ℕ → (X →L[ℂ] ℂ) →L[ℂ] ℂ :=
    fun n => NormedSpace.inclusionInDoubleDual ℂ X (s n)
  have hpointwise : ∀ f : X →L[ℂ] ℂ, ∃ C : ℝ, ∀ n, ‖g n f‖ ≤ C := by
    intro f
    obtain ⟨R, _, hR⟩ := cauchySeq_bdd (hs f)
    refine ⟨R + ‖f (s 0)‖, ?_⟩
    intro n
    change ‖f (s n)‖ ≤ _
    calc
      ‖f (s n)‖ = ‖(f (s n) - f (s 0)) + f (s 0)‖ := by congr 1; abel
      _ ≤ ‖f (s n) - f (s 0)‖ + ‖f (s 0)‖ := norm_add_le _ _
      _ ≤ R + ‖f (s 0)‖ := add_le_add_right (by simpa [dist_eq_norm] using (hR n 0).le) _
  obtain ⟨M, hM⟩ := complex_uniform_boundedness g hpointwise
  refine ⟨M, ?_⟩
  intro n
  have hnorm : ‖g n‖ = ‖s n‖ :=
    (NormedSpace.inclusionInDoubleDualLi ℂ (E := X)).norm_map (s n)
  rw [← hnorm]
  exact hM n

/-- Norm Cauchyness in a Banach space implies weak convergence. -/
theorem cauchySeq_weakly_convergent [CompleteSpace X] {s : ℕ → X}
    (hs : CauchySeq s) :
    ∃ x : X, ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (s n)) atTop (𝓝 (f x)) := by
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hs
  exact ⟨x, fun f => (f.continuous.tendsto x).comp hx⟩

/-- A non-Cauchy sequence has uniformly separated pairs in every tail. -/
theorem noncauchy_tail_pairs {s : ℕ → X} (hs : ¬ CauchySeq s) :
    ∃ r : ℝ, 0 < r ∧ ∀ N : ℕ, ∃ p q : ℕ,
      N ≤ p ∧ p < q ∧ r ≤ ‖s p - s q‖ := by
  classical
  rw [Metric.cauchySeq_iff] at hs
  push_neg at hs
  obtain ⟨r, hr, htail⟩ := hs
  refine ⟨r, hr, ?_⟩
  intro N
  obtain ⟨p, hp, q, hq, hpq⟩ := htail N
  have hneq : p ≠ q := by
    intro h
    subst q
    simp at hpq
    linarith
  rcases lt_or_gt_of_ne hneq with hpq' | hqp'
  · exact ⟨p, q, hp, hpq', by simpa [dist_eq_norm] using hpq⟩
  · exact ⟨q, p, hq, hqp', by simpa [dist_eq_norm, norm_sub_rev] using hpq⟩

/-- Successive separated pairs can be chosen recursively. -/
theorem noncauchy_successive_pairs {s : ℕ → X} (hs : ¬ CauchySeq s) :
    ∃ r : ℝ, 0 < r ∧ ∃ p q : ℕ → ℕ,
      (∀ n, p n < q n ∧ q n < p (n + 1)) ∧
      ∀ n, r ≤ ‖s (p n) - s (q n)‖ := by
  classical
  obtain ⟨r, hr, hpairs⟩ := noncauchy_tail_pairs hs
  choose p₀ q₀ hlow hlt hsep using hpairs
  let pairs : ℕ → ℕ × ℕ := Nat.rec (p₀ 0, q₀ 0)
    (fun _ v => (p₀ (v.2 + 1), q₀ (v.2 + 1)))
  have hnext (n : ℕ) : pairs (n + 1) =
      (p₀ ((pairs n).2 + 1), q₀ ((pairs n).2 + 1)) := rfl
  have hspec : ∀ n, (pairs n).1 < (pairs n).2 ∧
      r ≤ ‖s (pairs n).1 - s (pairs n).2‖ := by
    intro n
    cases n with
    | zero => exact ⟨hlt 0, hsep 0⟩
    | succ n => exact ⟨hlt _, hsep _⟩
  refine ⟨r, hr, fun n => (pairs n).1, fun n => (pairs n).2, ?_, fun n => (hspec n).2⟩
  intro n
  refine ⟨(hspec n).1, ?_⟩
  change (pairs n).2 < (pairs (n + 1)).1
  rw [hnext]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (hlow _)

end SurveyStatements.P1
