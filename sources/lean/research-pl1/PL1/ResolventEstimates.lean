import PL1.Definitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Resolvent algebra and the quantitative column estimates

These lemmas prove the elementary algebra and scalar estimates used in
Propositions 3.2 and 4.2. Operator hypotheses are explicit: this file does not
assert the existence of the product-measure resolvents.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators

namespace PL1.ResolventEstimates

/-- The geometric ratio in the dyadic projection estimates. -/
def dyadicRatio : ℝ := (Real.sqrt 2)⁻¹

theorem dyadicRatio_pos : 0 < dyadicRatio := by
  unfold dyadicRatio
  positivity

theorem dyadicRatio_nonneg : 0 ≤ dyadicRatio := dyadicRatio_pos.le

theorem dyadicRatio_lt_one : dyadicRatio < 1 := by
  have hs : 1 < Real.sqrt 2 := by
    have hp := Real.sqrt_nonneg (2 : ℝ)
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  exact inv_lt_one_of_one_lt₀ hs

theorem dyadicRatio_sq : dyadicRatio ^ 2 = (1 : ℝ) / 2 := by
  unfold dyadicRatio
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem dyadicRatio_eq_sqrt_div_two : dyadicRatio = Real.sqrt 2 / 2 := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold dyadicRatio
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  apply (inv_mul_eq_iff_eq_mul₀ hs).2
  nlinarith

theorem one_sub_dyadicRatio_pos : 0 < 1 - dyadicRatio :=
  sub_pos.2 dyadicRatio_lt_one

theorem geometric_summable : Summable (fun n : ℕ => dyadicRatio ^ n) :=
  summable_geometric_of_lt_one dyadicRatio_nonneg dyadicRatio_lt_one

theorem geometric_tsum : (∑' n : ℕ, dyadicRatio ^ n) = (1 - dyadicRatio)⁻¹ :=
  tsum_geometric_of_lt_one dyadicRatio_nonneg dyadicRatio_lt_one

theorem geometric_tail_summable : Summable (fun n : ℕ => dyadicRatio ^ (n + 1)) := by
  simpa only [pow_succ] using geometric_summable.mul_right dyadicRatio

theorem geometric_tail_tsum :
    (∑' n : ℕ, dyadicRatio ^ (n + 1)) = dyadicRatio / (1 - dyadicRatio) := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, geometric_tsum]
  ring

theorem projectionBound_eq :
    (1 + 2 * dyadicRatio) / (1 - dyadicRatio) = PL1.projectionBound := by
  apply (div_eq_iff (ne_of_gt one_sub_dyadicRatio_pos)).2
  rw [dyadicRatio_eq_sqrt_div_two, PL1.projectionBound]
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

theorem zeroth_column_bound :
    1 + 2 * (∑' n : ℕ, dyadicRatio ^ (n + 1)) = 3 + 2 * Real.sqrt 2 := by
  rw [geometric_tail_tsum]
  field_simp [ne_of_gt one_sub_dyadicRatio_pos]
  rw [dyadicRatio_eq_sqrt_div_two]
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

theorem zeroth_column_le_projectionBound :
    1 + 2 * (∑' n : ℕ, dyadicRatio ^ (n + 1)) ≤ PL1.projectionBound := by
  rw [zeroth_column_bound, PL1.projectionBound]
  have hs := Real.sqrt_nonneg (2 : ℝ)
  linarith

theorem column_expression_le (j : ℕ) :
    dyadicRatio ^ (j + 1) +
      2 * (∑ k ∈ Finset.range j, dyadicRatio ^ (k + 1)) +
      (∑' k : ℕ, dyadicRatio ^ k) ≤ PL1.projectionBound := by
  have hp : 0 ≤ dyadicRatio ^ (j + 1) := pow_nonneg dyadicRatio_nonneg _
  have hsum := geometric_tail_summable.sum_le_tsum (Finset.range (j + 1))
    (fun i _ => pow_nonneg dyadicRatio_nonneg (i + 1))
  rw [Finset.sum_range_succ] at hsum
  calc
    _ ≤ 2 * (∑' k : ℕ, dyadicRatio ^ (k + 1)) +
        (∑' k : ℕ, dyadicRatio ^ k) := by linarith
    _ = (1 + 2 * dyadicRatio) / (1 - dyadicRatio) := by
      rw [geometric_tail_tsum, geometric_tsum]
      ring
    _ = PL1.projectionBound := projectionBound_eq

/-- The column majorant in formula (4.5), with row index first. -/
def majorant : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | i + 1, 0 => 2 * dyadicRatio ^ (i + 1)
  | 0, j + 1 => dyadicRatio ^ (j + 1)
  | i + 1, j + 1 =>
      if i < j then 2 * dyadicRatio ^ (j - i) else dyadicRatio ^ (i - j)

theorem majorant_nonneg (i j : ℕ) : 0 ≤ majorant i j := by
  rcases i with _ | i <;> rcases j with _ | j <;> simp only [majorant]
  · norm_num
  · exact pow_nonneg dyadicRatio_nonneg _
  · exact mul_nonneg (by norm_num) (pow_nonneg dyadicRatio_nonneg _)
  · split_ifs
    · exact mul_nonneg (by norm_num) (pow_nonneg dyadicRatio_nonneg _)
    · exact pow_nonneg dyadicRatio_nonneg _

theorem majorant_summable (j : ℕ) : Summable (fun i => majorant i j) := by
  cases j with
  | zero =>
    apply (summable_nat_add_iff 1).1
    simpa only [majorant] using geometric_tail_summable.mul_left 2
  | succ j =>
    apply (summable_nat_add_iff (j + 1)).1
    apply geometric_summable.congr
    intro i
    simp [majorant, Nat.not_lt_of_ge (Nat.le_add_left j i)]

theorem majorant_zeroth_tsum :
    (∑' i, majorant i 0) = 3 + 2 * Real.sqrt 2 := by
  rw [(majorant_summable 0).tsum_eq_zero_add]
  simp only [majorant, tsum_mul_left]
  exact zeroth_column_bound

theorem majorant_positive_tsum (j : ℕ) :
    (∑' i, majorant i (j + 1)) = dyadicRatio ^ (j + 1) +
      2 * (∑ k ∈ Finset.range j, dyadicRatio ^ (k + 1)) +
      (∑' k : ℕ, dyadicRatio ^ k) := by
  rw [(majorant_summable (j + 1)).tsum_eq_zero_add]
  have htail : Summable (fun i => majorant (i + 1) (j + 1)) :=
    (summable_nat_add_iff 1).2 (majorant_summable (j + 1))
  rw [← htail.sum_add_tsum_nat_add j]
  have hfinite : (∑ i ∈ Finset.range j, majorant (i + 1) (j + 1)) =
      2 * (∑ k ∈ Finset.range j, dyadicRatio ^ (k + 1)) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hlt : j - 1 - i < j := by omega
    have heq : j - (j - 1 - i) = i + 1 := by omega
    simp [majorant, hlt, heq, mul_comm]
  rw [hfinite]
  have htail_eq : (fun i => majorant (i + j + 1) (j + 1)) =
      (fun i => dyadicRatio ^ i) := by
    funext i
    simp [majorant, Nat.not_lt_of_ge (Nat.le_add_left j i)]
  rw [htail_eq]
  simp only [majorant]
  ring

theorem majorant_tsum_le (j : ℕ) :
    (∑' i, majorant i j) ≤ PL1.projectionBound := by
  cases j with
  | zero =>
    rw [majorant_zeroth_tsum]
    rw [← zeroth_column_bound]
    exact zeroth_column_le_projectionBound
  | succ j =>
    rw [majorant_positive_tsum]
    exact column_expression_le j

theorem dyadicRatio_pow_ne_zero (n : ℕ) : dyadicRatio ^ n ≠ 0 :=
  pow_ne_zero n (ne_of_gt dyadicRatio_pos)

theorem dyadicRatio_sq_pow (n : ℕ) :
    (dyadicRatio ^ 2) ^ n = (dyadicRatio ^ n) ^ 2 := by
  rw [← pow_mul, Nat.mul_comm 2 n, pow_mul]

theorem dyadicRatio_pow_div {i j : ℕ} (hij : i ≤ j) :
    dyadicRatio ^ j / dyadicRatio ^ i = dyadicRatio ^ (j - i) := by
  apply (div_eq_iff (dyadicRatio_pow_ne_zero i)).2
  rw [← pow_add, Nat.sub_add_cancel hij]

/-- The estimate for a positive column and a row below its diagonal. -/
theorem weighted_ratio_below_diagonal {i j : ℕ} (hij : i ≤ j) :
    (dyadicRatio ^ (j + 1) / dyadicRatio ^ (i + 1)) *
      (2 * min 1 ((dyadicRatio ^ 2) ^ (i + 1) / (dyadicRatio ^ 2) ^ j)) ≤
      2 * dyadicRatio ^ (j - i) := by
  calc
    _ ≤ (dyadicRatio ^ (j + 1) / dyadicRatio ^ (i + 1)) * (2 * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
        (div_nonneg (pow_nonneg dyadicRatio_nonneg _) (pow_nonneg dyadicRatio_nonneg _))
    _ = 2 * dyadicRatio ^ (j - i) := by
      rw [dyadicRatio_pow_div (Nat.add_le_add_right hij 1)]
      simp [Nat.add_sub_add_right, mul_comm]

/-- Above the diagonal the square of the geometric ratio cancels the factor two. -/
theorem weighted_ratio_above_diagonal {i j : ℕ} (hji : j ≤ i) :
    (dyadicRatio ^ (j + 1) / dyadicRatio ^ (i + 1)) *
      (2 * min 1 ((dyadicRatio ^ 2) ^ (i + 1) / (dyadicRatio ^ 2) ^ j)) ≤
      dyadicRatio ^ (i - j) := by
  calc
    _ ≤ (dyadicRatio ^ (j + 1) / dyadicRatio ^ (i + 1)) *
        (2 * ((dyadicRatio ^ 2) ^ (i + 1) / (dyadicRatio ^ 2) ^ j)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
        (div_nonneg (pow_nonneg dyadicRatio_nonneg _) (pow_nonneg dyadicRatio_nonneg _))
    _ = dyadicRatio ^ (i - j) := by
      rw [dyadicRatio_sq_pow, dyadicRatio_sq_pow]
      rw [pow_succ, pow_succ]
      have hi : dyadicRatio ^ i = dyadicRatio ^ (i - j) * dyadicRatio ^ j := by
        rw [← pow_add, Nat.sub_add_cancel hji]
      rw [hi]
      field_simp [dyadicRatio_pow_ne_zero, ne_of_gt dyadicRatio_pos]
      nlinarith [dyadicRatio_sq]

/-- The complete scalar estimate for the nonzero rows and columns. -/
theorem weighted_ratio_le_majorant (i j : ℕ) :
    (dyadicRatio ^ (j + 1) / dyadicRatio ^ (i + 1)) *
      (2 * min 1 ((dyadicRatio ^ 2) ^ (i + 1) / (dyadicRatio ^ 2) ^ j)) ≤
      majorant (i + 1) (j + 1) := by
  by_cases hij : i < j
  · simpa only [majorant, ite_eq_left hij] using weighted_ratio_below_diagonal hij.le
  · simpa only [majorant, ite_eq_right hij] using weighted_ratio_above_diagonal (Nat.le_of_not_gt hij)

/-- The scalar estimate for the zeroth column. -/
theorem weighted_ratio_zero_column (i : ℕ) :
    (dyadicRatio ^ (i + 1))⁻¹ *
      (2 * min 1 ((dyadicRatio ^ 2) ^ (i + 1))) ≤ majorant (i + 1) 0 := by
  calc
    _ ≤ (dyadicRatio ^ (i + 1))⁻¹ * (2 * ((dyadicRatio ^ 2) ^ (i + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
        (inv_nonneg.2 (pow_nonneg dyadicRatio_nonneg _))
    _ = majorant (i + 1) 0 := by
      rw [dyadicRatio_sq_pow, majorant]
      field_simp [dyadicRatio_pow_ne_zero]

section Operators

variable {𝕜 Y : Type*} [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A contraction has defect from the identity of norm at most two. -/
theorem norm_id_sub_le_two (A : Y →L[𝕜] Y) (hA : ‖A‖ ≤ 1) :
    ‖ContinuousLinearMap.id 𝕜 Y - A‖ ≤ 2 := by
  calc
    _ ≤ ‖ContinuousLinearMap.id 𝕜 Y‖ + ‖A‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith [ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := Y)]

theorem norm_defect_comp_le_two (A B : Y →L[𝕜] Y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖(ContinuousLinearMap.id 𝕜 Y - A).comp B‖ ≤ 2 := by
  calc
    _ ≤ ‖ContinuousLinearMap.id 𝕜 Y - A‖ * ‖B‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * 1 := mul_le_mul (norm_id_sub_le_two A hA) hB (norm_nonneg _) (by norm_num)
    _ = 2 := by ring

theorem norm_comp_defect_le_two (A B : Y →L[𝕜] Y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖A.comp (ContinuousLinearMap.id 𝕜 Y - B)‖ ≤ 2 := by
  calc
    _ ≤ ‖A‖ * ‖ContinuousLinearMap.id 𝕜 Y - B‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 2 := mul_le_mul hA (norm_id_sub_le_two B hB) (norm_nonneg _) (by norm_num)
    _ = 2 := by ring

/-- The resolvent identity and contractivity give the estimate in Proposition 3.2.
Taking `c = (s / t : ℝ)` cast into `𝕜` gives the printed bound. -/
theorem norm_defect_comp_le (A B : Y →L[𝕜] Y) (c : 𝕜)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hres : (ContinuousLinearMap.id 𝕜 Y - A).comp B =
      c • A.comp (ContinuousLinearMap.id 𝕜 Y - B)) :
    ‖(ContinuousLinearMap.id 𝕜 Y - A).comp B‖ ≤ 2 * min 1 ‖c‖ := by
  rw [mul_min_of_nonneg (1 : ℝ) ‖c‖ (by norm_num : (0 : ℝ) ≤ 2)]
  refine le_min ?_ ?_
  · simpa using norm_defect_comp_le_two A B hA hB
  · calc
      _ = ‖c‖ * ‖A.comp (ContinuousLinearMap.id 𝕜 Y - B)‖ := by rw [hres, norm_smul]
      _ ≤ ‖c‖ * 2 := mul_le_mul_of_nonneg_left
        (norm_comp_defect_le_two A B hA hB) (norm_nonneg _)
      _ = 2 * ‖c‖ := mul_comm _ _

theorem norm_defect_comp_le_real (A B : Y →L[𝕜] Y) (c : ℝ) (hc : 0 ≤ c)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hres : (ContinuousLinearMap.id 𝕜 Y - A).comp B =
      (c : 𝕜) • A.comp (ContinuousLinearMap.id 𝕜 Y - B)) :
    ‖(ContinuousLinearMap.id 𝕜 Y - A).comp B‖ ≤ 2 * min 1 c := by
  simpa only [RCLike.norm_ofReal, abs_of_nonneg hc] using
    norm_defect_comp_le A B (c : 𝕜) hA hB hres

/-- The weighted analysis coordinates used to define the intrinsic graph space. -/
def analysisCoordinate (S : ℕ → Y →L[𝕜] Y) : ℕ → Y →L[𝕜] Y
  | 0 => ContinuousLinearMap.id 𝕜 Y
  | n + 1 => (((dyadicRatio ^ (n + 1))⁻¹ : ℝ) : 𝕜) •
      (ContinuousLinearMap.id 𝕜 Y - S (n + 1))

/-- The columns used to synthesize the retraction. -/
def synthesisCoordinate (S : ℕ → Y →L[𝕜] Y) : ℕ → Y →L[𝕜] Y
  | 0 => S 0
  | n + 1 => ((dyadicRatio ^ (n + 1) : ℝ) : 𝕜) • S n

theorem synthesisCoordinate_norm_le_one (S : ℕ → Y →L[𝕜] Y)
    (hS : ∀ n, ‖S n‖ ≤ 1) (j : ℕ) : ‖synthesisCoordinate S j‖ ≤ 1 := by
  cases j with
  | zero => exact hS 0
  | succ j =>
    rw [synthesisCoordinate, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (pow_nonneg dyadicRatio_nonneg _)]
    calc
      _ ≤ dyadicRatio ^ (j + 1) * 1 :=
        mul_le_mul_of_nonneg_left (hS j) (pow_nonneg dyadicRatio_nonneg _)
      _ ≤ 1 := by simpa using pow_le_one₀ dyadicRatio_nonneg dyadicRatio_lt_one.le

/-- Every block has the explicit geometric majorant from the paper. -/
theorem weighted_block_norm_le_majorant (S : ℕ → Y →L[𝕜] Y)
    (hS : ∀ n, ‖S n‖ ≤ 1)
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j))
    (i j : ℕ) :
    ‖(analysisCoordinate S i).comp (synthesisCoordinate S j)‖ ≤ majorant i j := by
  cases i with
  | zero =>
    cases j with
    | zero => simpa [analysisCoordinate, synthesisCoordinate, majorant] using hS 0
    | succ j =>
      simp only [analysisCoordinate, synthesisCoordinate, ContinuousLinearMap.id_comp,
        norm_smul, RCLike.norm_ofReal, abs_of_nonneg (pow_nonneg dyadicRatio_nonneg _), majorant]
      simpa using mul_le_mul_of_nonneg_left (hS j) (pow_nonneg dyadicRatio_nonneg (j + 1))
  | succ i =>
    cases j with
    | zero =>
      have hb := norm_defect_comp_le_real (S (i + 1)) (S 0)
        ((dyadicRatio ^ 2) ^ (i + 1)) (pow_nonneg (sq_nonneg _) _)
        (hS (i + 1)) (hS 0) (by simpa using hres (i + 1) 0)
      rw [analysisCoordinate, synthesisCoordinate, ContinuousLinearMap.smul_comp,
        norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (inv_nonneg.2 (pow_nonneg dyadicRatio_nonneg _))]
      exact (mul_le_mul_of_nonneg_left hb
        (inv_nonneg.2 (pow_nonneg dyadicRatio_nonneg _))).trans (weighted_ratio_zero_column i)
    | succ j =>
      have hc : 0 ≤ (dyadicRatio ^ 2) ^ (i + 1) / (dyadicRatio ^ 2) ^ j :=
        div_nonneg (pow_nonneg (sq_nonneg _) _) (pow_nonneg (sq_nonneg _) _)
      have hb := norm_defect_comp_le_real (S (i + 1)) (S j)
        ((dyadicRatio ^ 2) ^ (i + 1) / (dyadicRatio ^ 2) ^ j) hc
        (hS (i + 1)) (hS j) (hres (i + 1) j)
      rw [analysisCoordinate, synthesisCoordinate, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_smul, norm_smul, norm_smul,
        RCLike.norm_ofReal, RCLike.norm_ofReal,
        abs_of_nonneg (inv_nonneg.2 (pow_nonneg dyadicRatio_nonneg _)),
        abs_of_nonneg (pow_nonneg dyadicRatio_nonneg _)]
      calc
        _ = (dyadicRatio ^ (j + 1) / dyadicRatio ^ (i + 1)) *
            ‖(ContinuousLinearMap.id 𝕜 Y - S (i + 1)).comp (S j)‖ := by ring
        _ ≤ (dyadicRatio ^ (j + 1) / dyadicRatio ^ (i + 1)) *
            (2 * min 1 ((dyadicRatio ^ 2) ^ (i + 1) / (dyadicRatio ^ 2) ^ j)) :=
          mul_le_mul_of_nonneg_left hb
            (div_nonneg (pow_nonneg dyadicRatio_nonneg _) (pow_nonneg dyadicRatio_nonneg _))
        _ ≤ majorant (i + 1) (j + 1) := weighted_ratio_le_majorant i j

theorem weighted_block_norm_summable (S : ℕ → Y →L[𝕜] Y)
    (hS : ∀ n, ‖S n‖ ≤ 1)
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j)) (j : ℕ) :
    Summable (fun i => ‖(analysisCoordinate S i).comp (synthesisCoordinate S j)‖) :=
  (majorant_summable j).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => weighted_block_norm_le_majorant S hS hres i j)

theorem weighted_block_norm_tsum_le (S : ℕ → Y →L[𝕜] Y)
    (hS : ∀ n, ‖S n‖ ≤ 1)
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j)) (j : ℕ) :
    (∑' i, ‖(analysisCoordinate S i).comp (synthesisCoordinate S j)‖) ≤ PL1.projectionBound :=
  (Summable.tsum_le_tsum (fun i => weighted_block_norm_le_majorant S hS hres i j)
    (weighted_block_norm_summable S hS hres j) (majorant_summable j)).trans (majorant_tsum_le j)

theorem weighted_column_apply_norm_summable (S : ℕ → Y →L[𝕜] Y)
    (hS : ∀ n, ‖S n‖ ≤ 1)
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j)) (j : ℕ) (x : Y) :
    Summable (fun i => ‖analysisCoordinate S i (synthesisCoordinate S j x)‖) := by
  apply ((weighted_block_norm_summable S hS hres j).mul_right ‖x‖).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro i
  exact ((analysisCoordinate S i).comp (synthesisCoordinate S j)).le_opNorm x

/-- A synthesis column maps into the intrinsic graph domain with norm at most C. -/
theorem weighted_column_apply_norm_tsum_le (S : ℕ → Y →L[𝕜] Y)
    (hS : ∀ n, ‖S n‖ ≤ 1)
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j)) (j : ℕ) (x : Y) :
    (∑' i, ‖analysisCoordinate S i (synthesisCoordinate S j x)‖) ≤
      PL1.projectionBound * ‖x‖ := by
  calc
    _ ≤ ∑' i, ‖(analysisCoordinate S i).comp (synthesisCoordinate S j)‖ * ‖x‖ :=
      Summable.tsum_le_tsum
        (fun i => ((analysisCoordinate S i).comp (synthesisCoordinate S j)).le_opNorm x)
        (weighted_column_apply_norm_summable S hS hres j x)
        ((weighted_block_norm_summable S hS hres j).mul_right ‖x‖)
    _ = (∑' i, ‖(analysisCoordinate S i).comp (synthesisCoordinate S j)‖) * ‖x‖ :=
      tsum_mul_right
    _ ≤ PL1.projectionBound * ‖x‖ :=
      mul_le_mul_of_nonneg_right (weighted_block_norm_tsum_le S hS hres j) (norm_nonneg _)

/-- The half-ratio resolvent identity yields the dyadic telescoping relation. -/
theorem dyadic_telescoping (A B : Y →L[𝕜] Y)
    (hcomm : A.comp B = B.comp A)
    (hres : (ContinuousLinearMap.id 𝕜 Y - B).comp A =
      (2 : 𝕜)⁻¹ • B.comp (ContinuousLinearMap.id 𝕜 Y - A)) :
    A.comp (ContinuousLinearMap.id 𝕜 Y - B) = B - A := by
  ext x
  have h := congrArg (fun T : Y →L[𝕜] Y => T x) hres
  have hc := congrArg (fun T : Y →L[𝕜] Y => T x) hcomm
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_apply, map_sub] at h hc ⊢
  rw [hc]
  linear_combination (norm := module) (2 : 𝕜) • h

/-- Specialization of the resolvent family identity to neighboring dyadic scales. -/
theorem dyadic_family_telescoping (S : ℕ → Y →L[𝕜] Y)
    (hcomm : ∀ i j, (S i).comp (S j) = (S j).comp (S i))
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j)) (n : ℕ) :
    (S n).comp (ContinuousLinearMap.id 𝕜 Y - S (n + 1)) = S (n + 1) - S n := by
  apply dyadic_telescoping (S n) (S (n + 1)) (hcomm n (n + 1))
  have hr : (dyadicRatio ^ 2) ^ (n + 1) / (dyadicRatio ^ 2) ^ n = (1 : ℝ) / 2 := by
    rw [pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero n (dyadicRatio_pow_ne_zero 2))]
    exact dyadicRatio_sq
  simpa only [hr, RCLike.ofReal_div, RCLike.ofReal_inv, RCLike.ofReal_one,
    RCLike.ofReal_ofNat, one_div]
    using hres (n + 1) n

/-- The weights cancel in each nonzero term of the synthesis-after-analysis map. -/
theorem weighted_composition_telescoping (S : ℕ → Y →L[𝕜] Y)
    (hcomm : ∀ i j, (S i).comp (S j) = (S j).comp (S i))
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j)) (n : ℕ) :
    (synthesisCoordinate S (n + 1)).comp (analysisCoordinate S (n + 1)) =
      S (n + 1) - S n := by
  rw [synthesisCoordinate, analysisCoordinate, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul]
  have hw : ((dyadicRatio ^ (n + 1) : ℝ) : 𝕜) *
      (((dyadicRatio ^ (n + 1))⁻¹ : ℝ) : 𝕜) = 1 := by
    rw [← RCLike.ofReal_mul, mul_inv_cancel₀ (dyadicRatio_pow_ne_zero _), RCLike.ofReal_one]
  rw [hw, one_smul]
  exact dyadic_family_telescoping S hcomm hres n

/-- Every finite synthesis-after-analysis sum is exactly the last resolvent. -/
theorem weighted_composition_partial_sum (S : ℕ → Y →L[𝕜] Y)
    (hcomm : ∀ i j, (S i).comp (S j) = (S j).comp (S i))
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j)) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (synthesisCoordinate S j).comp (analysisCoordinate S j)) =
      S N := by
  induction N with
  | zero => simp [analysisCoordinate, synthesisCoordinate]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, weighted_composition_telescoping S hcomm hres N]
    abel

theorem weighted_composition_partial_sum_apply (S : ℕ → Y →L[𝕜] Y)
    (hcomm : ∀ i j, (S i).comp (S j) = (S j).comp (S i))
    (hres : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - S i).comp (S j) =
      (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
        (S i).comp (ContinuousLinearMap.id 𝕜 Y - S j)) (N : ℕ) (y : Y) :
    (∑ j ∈ Finset.range (N + 1), synthesisCoordinate S j (analysisCoordinate S j y)) = S N y := by
  have h := congrArg (fun T : Y →L[𝕜] Y => T y) (weighted_composition_partial_sum S hcomm hres N)
  simpa using h

end Operators

/-- The scalar version of the resolvent identity, used on Walsh characters. -/
theorem scalar_resolvent_identity {s t a : ℝ} (hs : 0 < s) (ht : 0 < t)
    (ha : 0 ≤ a) :
    (1 - (1 + s * a)⁻¹) * (1 + t * a)⁻¹ =
      (s / t) * (1 + s * a)⁻¹ * (1 - (1 + t * a)⁻¹) := by
  have hs' : 1 + s * a ≠ 0 := ne_of_gt (by positivity)
  have ht' : 1 + t * a ≠ 0 := ne_of_gt (by positivity)
  field_simp [hs', ht', ne_of_gt ht]
  ring

end PL1.ResolventEstimates
