import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! Finite and absolutely summable telescopes with a prescribed starting
index. These identify the error-series actions on individual Haar vectors. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P5

theorem sum_range_tail_differences {E : Type*} [AddCommGroup E]
    (G : ℕ → E) (j N : ℕ) :
    (∑ k ∈ Finset.range N, if j ≤ k then G k - G (k + 1) else 0) =
      if j ≤ N then G j - G N else 0 := by
  induction N with
  | zero =>
      by_cases hj : j = 0
      · subst j; simp
      · simp [hj]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hj : j ≤ N
      · rw [if_pos hj, if_pos hj, if_pos (show j ≤ N + 1 from by omega)]
        abel
      · rw [if_neg hj, if_neg hj, zero_add]
        by_cases hnext : j ≤ N + 1
        · have heq : j = N + 1 := by omega
          rw [if_pos hnext, heq, sub_self]
        · rw [if_neg hnext]

theorem tsum_tail_differences {E : Type*} [NormedAddCommGroup E]
    (G : ℕ → E) (M : E) (j : ℕ) (hG : Tendsto G atTop (𝓝 M))
    (hs : Summable (fun k => if j ≤ k then G k - G (k + 1) else 0)) :
    (∑' k, if j ≤ k then G k - G (k + 1) else 0) = G j - M := by
  have hfinite : ∀ᶠ N in atTop,
      (∑ k ∈ Finset.range N, if j ≤ k then G k - G (k + 1) else 0) = G j - G N := by
    filter_upwards [eventually_ge_atTop j] with N hN
    rw [sum_range_tail_differences, if_pos hN]
  have hlimit : Tendsto
      (fun N => ∑ k ∈ Finset.range N, if j ≤ k then G k - G (k + 1) else 0)
      atTop (𝓝 (G j - M)) :=
    (tendsto_const_nhds.sub hG).congr' (Filter.EventuallyEq.symm hfinite)
  exact tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlimit

theorem tsum_window_differences {E : Type*} [NormedAddCommGroup E]
    (G : ℕ → E) (j r : ℕ) (hjr : j ≤ r) :
    (∑' k, if j ≤ k ∧ k < r then G (k + 1) - G k else 0) = G r - G j := by
  rw [tsum_eq_sum (s := Finset.range r) (fun k hk => by
    have hkr : ¬ k < r := by simpa only [Finset.mem_range] using hk
    simp [hkr])]
  have hsum := sum_range_tail_differences (fun k => -G k) j r
  rw [if_pos hjr] at hsum
  simpa only [Finset.mem_range, neg_sub_neg] using
    (show (∑ k ∈ Finset.range r,
      if j ≤ k ∧ k < r then -G k - -G (k + 1) else 0) = -G j - -G r from by
      calc
        _ = ∑ k ∈ Finset.range r, if j ≤ k then -G k - -G (k + 1) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_range.mp hk, and_true]
        _ = _ := hsum)

end SurveyStatements.P5

