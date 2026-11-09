import PL1.SchurBoundedCompleteness

/-! # Bounded completeness from unconditional sign bounds in Schur spaces -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace PL1.UnconditionalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The constant block followed by successive differences of partial-sum projections. -/
def difference (P : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => P 0
  | n + 1 => P (n + 1) - P n

/-- Differences of a coherent branch, including its initial vector. -/
def branchDifference (x : ℕ → E) : ℕ → E
  | 0 => x 0
  | n + 1 => x (n + 1) - x n

theorem difference_branch (P : ℕ → E →L[ℝ] E) (x : ℕ → E)
    (hx : ∀ m n, m ≤ n → P m (x n) = x m)
    (N j : ℕ) (hj : j ≤ N) : difference P j (x N) = branchDifference x j := by
  cases j with
  | zero => exact hx 0 N (Nat.zero_le _)
  | succ j =>
    simp only [difference, branchDifference, sub_apply, hx (j + 1) N hj,
      hx j N (Nat.le_trans (Nat.le_succ j) hj)]

omit [NormedSpace ℝ E] in
theorem sum_branchDifference (x : ℕ → E) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), branchDifference x j) = x N := by
  induction N with
  | zero => simp [branchDifference]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, branchDifference]
    abel

/-- A bounded coherent branch has bounded signed sums of its successive differences. -/
theorem signedSumsBounded_branchDifference
    (P : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (htransform : ∀ (N : ℕ) (ε : ℕ → ℝ) (y : E),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), ε j • difference P j y‖ ≤ C * ‖y‖)
    (x : ℕ → E) (hx : ∀ m n, m ≤ n → P m (x n) = x m)
    (M : ℝ) (hM : ∀ n, ‖x n‖ ≤ M) :
    SchurBoundedCompleteness.SignedSumsBounded (branchDifference x) (C * M) := by
  intro N ε hε
  cases N with
  | zero =>
    have hM0 : 0 ≤ M := (norm_nonneg (x 0)).trans (hM 0)
    simpa using mul_nonneg hC hM0
  | succ N =>
    calc
      _ = ‖∑ j ∈ Finset.range (N + 1), ε j • difference P j (x N)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [difference_branch P x hx N j (by have := Finset.mem_range.mp hj; omega)]
      _ ≤ C * ‖x N‖ := htransform N ε (x N) hε
      _ ≤ C * M := mul_le_mul_of_nonneg_left (hM N) hC

/-- In a complete real Schur space, a uniform unconditional sign bound forces every
bounded coherent branch of partial-sum projections to converge in norm. -/
theorem bounded_branch_converges [CompleteSpace E]
    (hS : HasSchurProperty ℝ E)
    (P : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (htransform : ∀ (N : ℕ) (ε : ℕ → ℝ) (y : E),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), ε j • difference P j y‖ ≤ C * ‖y‖)
    (x : ℕ → E) (hx : ∀ m n, m ≤ n → P m (x n) = x m)
    (hbounded : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) :
    ∃ a : E, Tendsto x atTop (𝓝 a) := by
  obtain ⟨M, hM⟩ := hbounded
  obtain ⟨a, ha⟩ := SchurBoundedCompleteness.exists_tendsto_partialSums_of_signed_sums_bounded
    hS (branchDifference x) (C * M)
      (signedSumsBounded_branchDifference P C hC htransform x hx M hM)
  refine ⟨a, ?_⟩
  have h := ha.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, sum_branchDifference] using h

end PL1.UnconditionalDecomposition
