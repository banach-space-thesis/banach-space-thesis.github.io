import PL1.DyadicInterpolationIntegral
import Mathlib.Tactic.GCongr

/-! Explicit universal constants for the dyadic interpolation comparison. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PL1.DyadicInterpolation

theorem weight_eq_sqrt_two_pow (n : ℕ) : weight n = (Real.sqrt 2) ^ n := by
  have hh : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) = Real.sqrt 2 := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg_eq_inv_rpow]
    norm_num [Real.sqrt_eq_rpow]
  induction n with
  | zero => simp [weight]
  | succ n ih => rw [weight_succ, ih, hh, pow_succ]

theorem quarter_le_lowerConstant : (1 / 4 : ℝ) ≤ lowerConstant := by
  have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  rw [Real.rpow_one] at h
  unfold lowerConstant
  linarith

theorem upperConstant_le_two : upperConstant ≤ 2 := by
  have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (by norm_num : (-2 : ℝ) ≤ -3 / 2)
  norm_num [Real.rpow_neg_natCast] at h
  unfold upperConstant
  linarith

@[simp] theorem sample_zero (k : ℝ → ℝ) : sample k 0 = ENNReal.ofReal (k 1) := by
  simp [sample, weight]

def discreteNorm (k : ℝ → ℝ) : ℝ≥0∞ := ENNReal.ofReal (k 1) + ∑' n, sample k (n + 1)

theorem discreteNorm_eq_tsum (k : ℝ → ℝ) : discreteNorm k = ∑' n, sample k n := by
  rw [tsum_eq_zero_add' ENNReal.summable, sample_zero]
  rfl

variable {k : ℝ → ℝ}

theorem fullIntegral_le_four_discreteNorm (hk : ∀ t ∈ Ici (0 : ℝ), 0 ≤ k t)
    (hmono : MonotoneOn k (Ici (0 : ℝ)))
    (htail : ∀ t, 1 ≤ t → k t = k 1) :
    fullIntegral k ≤ 4 * discreteNorm k := by
  have hu : smallIntegral k ≤ 2 * discreteNorm k := by
    calc
      _ ≤ ENNReal.ofReal upperConstant * discreteNorm k := by
        rw [discreteNorm_eq_tsum]
        exact (smallIntegral_bounds hk hmono).2
      _ ≤ 2 * discreteNorm k := by
        gcongr
        exact_mod_cast ENNReal.ofReal_le_ofReal upperConstant_le_two
  have hz : ENNReal.ofReal (k 1) ≤ discreteNorm k := le_self_add
  rw [fullIntegral_eq (hk 1 (by norm_num)) htail,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  calc
    _ ≤ 2 * discreteNorm k + 2 * discreteNorm k := add_le_add hu (by gcongr)
    _ = 4 * discreteNorm k := by rw [← add_mul]; norm_num

theorem discreteNorm_le_five_fullIntegral (hk : ∀ t ∈ Ici (0 : ℝ), 0 ≤ k t)
    (hmono : MonotoneOn k (Ici (0 : ℝ)))
    (htail : ∀ t, 1 ≤ t → k t = k 1) :
    discreteNorm k ≤ 5 * fullIntegral k := by
  have hs : smallIntegral k ≤ fullIntegral k := by
    rw [fullIntegral_eq (hk 1 (by norm_num)) htail]
    exact le_self_add
  have hl : (1 / 4 : ℝ≥0∞) * (∑' n, sample k (n + 1)) ≤ fullIntegral k := by
    calc
      _ ≤ ENNReal.ofReal lowerConstant * (∑' n, sample k (n + 1)) := by
        gcongr
        have h := ENNReal.ofReal_le_ofReal quarter_le_lowerConstant
        simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h
      _ ≤ smallIntegral k := (smallIntegral_bounds hk hmono).1
      _ ≤ fullIntegral k := hs
  have hsum : (∑' n, sample k (n + 1)) ≤ 4 * fullIntegral k := by
    have h : 4 * ((1 / 4 : ℝ≥0∞) * (∑' n, sample k (n + 1))) ≤ 4 * fullIntegral k := by
      gcongr
    simpa only [← mul_assoc, one_div,
      ENNReal.mul_inv_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by finiteness : (4 : ℝ≥0∞) ≠ ⊤),
      one_mul] using h
  have hz : ENNReal.ofReal (k 1) ≤ fullIntegral k := by
    calc
      _ ≤ ENNReal.ofReal (2 * k 1) := ENNReal.ofReal_le_ofReal (by nlinarith [hk 1 (by norm_num)])
      _ ≤ fullIntegral k := by
        rw [fullIntegral_eq (hk 1 (by norm_num)) htail]
        exact le_add_self
  unfold discreteNorm
  calc
    _ ≤ fullIntegral k + 4 * fullIntegral k := add_le_add hz hsum
    _ = (1 + 4) * fullIntegral k := by rw [add_mul, one_mul]
    _ = 5 * fullIntegral k := by norm_num

theorem fullIntegral_ne_top_iff_discreteNorm (hk : ∀ t ∈ Ici (0 : ℝ), 0 ≤ k t)
    (hmono : MonotoneOn k (Ici (0 : ℝ)))
    (htail : ∀ t, 1 ≤ t → k t = k 1) :
    fullIntegral k ≠ ⊤ ↔ discreteNorm k ≠ ⊤ := by
  rw [fullIntegral_ne_top_iff hk hmono htail, discreteNorm, ENNReal.add_ne_top]
  exact (and_iff_right ENNReal.ofReal_ne_top).symm

end PL1.DyadicInterpolation
