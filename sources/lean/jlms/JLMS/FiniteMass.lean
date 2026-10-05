import Mathlib.Tactic

/-!
# The finite-mass contradiction in Lemma 5.4

This is the numerical core of the paper's essential-weight argument. After
choosing N disjoint neighborhoods, their masses have sum at most ‖T‖. If
N ε > ‖T‖, at least one neighborhood has mass < ε arbitrarily late.
The topology and the atomic representation of functionals are separate inputs
to that application; this lemma does not assert those missing constructions.
-/

namespace JLMS

/-- A bounded total mass cannot eventually put ε on every one of N pieces
when N ε exceeds the bound. No positivity of the individual weights is needed. -/
theorem exists_arbitrarily_late_small_of_sum_le
    {N : ℕ} (w : Fin N → ℕ → ℝ) (M ε : ℝ)
    (hbudget : ∀ j, ∑ i : Fin N, w i j ≤ M)
    (hlarge : M < N * ε) :
    ∃ i : Fin N, ∀ J : ℕ, ∃ j : ℕ, J < j ∧ w i j < ε := by
  classical
  by_contra h
  push_neg at h
  choose threshold hthreshold using h
  let j := (Finset.univ.sup threshold) + 1
  have hmass (i : Fin N) : ε ≤ w i j := by
    apply hthreshold i j
    exact lt_of_le_of_lt (Finset.le_sup (f := threshold) (Finset.mem_univ i))
      (Nat.lt_succ_self _)
  have hsum : (N : ℝ) * ε ≤ ∑ i : Fin N, w i j := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmass i)
  exact (not_lt_of_ge (hsum.trans (hbudget j))) hlarge

/-- The small-weight indices can be selected as one strictly increasing sequence.
This is the extraction step in Corollary 5.5, usable for any predicate on ℕ. -/
theorem exists_strictMono_of_arbitrarily_late (P : ℕ → Prop)
    (hP : ∀ J : ℕ, ∃ j : ℕ, J < j ∧ P j) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n, P (s n) := by
  classical
  choose next hnext using hP
  let s : ℕ → ℕ := fun n => Nat.rec (next 0) (fun _ previous => next previous) n
  refine ⟨s, strictMono_nat_of_lt_succ (fun n => (hnext (s n)).1), ?_⟩
  intro n
  cases n with
  | zero => exact (hnext 0).2
  | succ n => exact (hnext (s n)).2

end JLMS
