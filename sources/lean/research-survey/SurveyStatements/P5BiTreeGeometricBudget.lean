import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! A positive geometric accuracy array with uniform control of all four
error-series budgets. The constants leave room for the root scalar error. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P5

def biTreeAccuracy (ε : ℝ) (i j : ℕ) : ℝ :=
  ε / 1024 * (1 / 4 : ℝ) ^ i * (1 / 4 : ℝ) ^ j

def biTreeErrorMajorant (ε : ℝ) (k : ℕ) : ℝ := ε / 256 * (1 / 2 : ℝ) ^ k

theorem biTreeAccuracy_pos {ε : ℝ} (hε : 0 < ε) (i j : ℕ) :
    0 < biTreeAccuracy ε i j := by unfold biTreeAccuracy; positivity

theorem level_count_le_two_pow (k : ℕ) : (k + 1 : ℕ) ≤ (2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

theorem biTreeAccuracy_le_row {ε : ℝ} (hε : 0 ≤ ε) (k j : ℕ) :
    biTreeAccuracy ε k j ≤ ε / 1024 * (1 / 4 : ℝ) ^ k := by
  unfold biTreeAccuracy
  exact (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (n := j) (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num))
    (by positivity)).trans_eq (mul_one _)

theorem biTreeAccuracy_le_column {ε : ℝ} (hε : 0 ≤ ε) (i k : ℕ) :
    biTreeAccuracy ε i k ≤ ε / 1024 * (1 / 4 : ℝ) ^ k := by
  have h := biTreeAccuracy_le_row hε k i
  simpa only [biTreeAccuracy, mul_assoc, mul_comm, mul_left_comm] using h

theorem weighted_quarter_geometric_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    4 * (k + 1 : ℕ) * (ε / 1024 * (1 / 4 : ℝ) ^ k) ≤ biTreeErrorMajorant ε k := by
  have h := mul_le_mul_of_nonneg_right (level_count_le_two_pow k)
    (show 0 ≤ 4 * (ε / 1024) * (1 / 4 : ℝ) ^ k by positivity)
  have hpow : (2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  calc
    _ ≤ 4 * (2 : ℝ) ^ k * (ε / 1024 * (1 / 4 : ℝ) ^ k) := by nlinarith [h]
    _ = biTreeErrorMajorant ε k := by unfold biTreeErrorMajorant; rw [show
      4 * (2 : ℝ) ^ k * (ε / 1024 * (1 / 4 : ℝ) ^ k) =
        (ε / 256) * ((2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k) by ring, hpow]

theorem biTreeAccuracy_diagonal_budget_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    4 * (k + 1 : ℕ) * biTreeAccuracy ε k k ≤ biTreeErrorMajorant ε k :=
  (mul_le_mul_of_nonneg_left (biTreeAccuracy_le_row hε k k) (by positivity)).trans
    (weighted_quarter_geometric_le hε k)

theorem biTreeAccuracy_superdiagonal_budget_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    4 * (k + 1 : ℕ) * biTreeAccuracy ε k (k + 1) ≤ biTreeErrorMajorant ε k :=
  (mul_le_mul_of_nonneg_left (biTreeAccuracy_le_row hε k (k + 1)) (by positivity)).trans
    (weighted_quarter_geometric_le hε k)

theorem biTreeAccuracy_lower_budget_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    4 * ∑ j ∈ Finset.range (k + 1), biTreeAccuracy ε k j ≤ biTreeErrorMajorant ε k := by
  have hsum : (∑ j ∈ Finset.range (k + 1), biTreeAccuracy ε k j) ≤
      (k + 1 : ℕ) * (ε / 1024 * (1 / 4 : ℝ) ^ k) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (k + 1), ε / 1024 * (1 / 4 : ℝ) ^ k :=
        Finset.sum_le_sum (fun j _ => biTreeAccuracy_le_row hε k j)
      _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)).trans
    (by simpa only [mul_assoc] using weighted_quarter_geometric_le hε k)

theorem biTreeAccuracy_upper_budget_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    4 * ∑ i ∈ Finset.range k, biTreeAccuracy ε i k ≤ biTreeErrorMajorant ε k := by
  have hsum : (∑ i ∈ Finset.range k, biTreeAccuracy ε i k) ≤
      (k + 1 : ℕ) * (ε / 1024 * (1 / 4 : ℝ) ^ k) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, ε / 1024 * (1 / 4 : ℝ) ^ k :=
        Finset.sum_le_sum (fun i _ => biTreeAccuracy_le_column hε i k)
      _ = (k : ℝ) * (ε / 1024 * (1 / 4 : ℝ) ^ k) := by simp
      _ ≤ _ := by gcongr; exact_mod_cast Nat.le_succ k
  exact (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)).trans
    (by simpa only [mul_assoc] using weighted_quarter_geometric_le hε k)

theorem biTree_budget_summable_bound {ε : ℝ} (hε : 0 ≤ ε) (b : ℕ → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hle : ∀ k, b k ≤ biTreeErrorMajorant ε k) :
    Summable b ∧ (∑' k, b k) ≤ ε / 128 := by
  have hmajor : Summable (biTreeErrorMajorant ε) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (ε / 256)
  have hsum : Summable b := Summable.of_nonneg_of_le hb hle hmajor
  refine ⟨hsum, (hsum.tsum_le_tsum hle hmajor).trans_eq ?_⟩
  unfold biTreeErrorMajorant
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  ring

theorem biTreeAccuracy_diagonal_summable_bound {ε : ℝ} (hε : 0 ≤ ε) :
    Summable (fun k => biTreeAccuracy ε k k) ∧
      (∑' k, biTreeAccuracy ε k k) ≤ ε / 128 := by
  apply biTree_budget_summable_bound hε _
  · intro k; unfold biTreeAccuracy; positivity
  · intro k
    have hb := biTreeAccuracy_diagonal_budget_le hε k
    have hη : 0 ≤ biTreeAccuracy ε k k := by unfold biTreeAccuracy; positivity
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact (show biTreeAccuracy ε k k ≤ 4 * (k + 1 : ℕ) * biTreeAccuracy ε k k by
      push_cast; nlinarith).trans hb

theorem biTreeAccuracy_superdiagonal_summable_bound {ε : ℝ} (hε : 0 ≤ ε) :
    Summable (fun k => biTreeAccuracy ε k (k + 1)) ∧
      (∑' k, biTreeAccuracy ε k (k + 1)) ≤ ε / 128 := by
  apply biTree_budget_summable_bound hε _
  · intro k; unfold biTreeAccuracy; positivity
  · intro k
    have hb := biTreeAccuracy_superdiagonal_budget_le hε k
    have hη : 0 ≤ biTreeAccuracy ε k (k + 1) := by unfold biTreeAccuracy; positivity
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact (show biTreeAccuracy ε k (k + 1) ≤
      4 * (k + 1 : ℕ) * biTreeAccuracy ε k (k + 1) by
      push_cast; nlinarith).trans hb

end SurveyStatements.P5
