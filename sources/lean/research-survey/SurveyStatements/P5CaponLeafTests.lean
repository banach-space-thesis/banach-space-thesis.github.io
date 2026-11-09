import SurveyStatements.P5RademacherDecay
import SurveyStatements.P5L1VariationImages
import SurveyStatements.P5L1SetReaders

/-! Actual normalized leftmost dyadic leaf tests, their Haar expansions
and their values on the disjoint rings used for the Capon counterexample. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace SurveyStatements.P5

def leftDyadicIndex (n : ℕ) : DyadicIndex := ⟨n, ⟨0, by positivity⟩⟩

def leftDyadicBranch : P5L1Variation.DyadicBranch 0 where
  index j := ⟨0, by positivity⟩
  parent j := by
    apply Fin.ext
    simp [P5Support.lpHaarParentIndex]

def leftLeafTest (N : ℕ) : Lp ℝ 1 unitIntervalMeasure := leftDyadicBranch.leafTest ℝ N

theorem leftLeafTest_norm_le (N : ℕ) : ‖leftLeafTest N‖ ≤ 2 :=
  leftDyadicBranch.leafTest_norm_le ℝ N

theorem leftLeafTest_eq_sum (N : ℕ) :
    leftLeafTest N = ∑ k ∈ Finset.range N, (2 : ℝ) ^ k • dyadicHaar ℝ 1 (leftDyadicIndex k) := by
  rw [leftLeafTest, leftDyadicBranch.leafTest_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  change P5L1Variation.cellDensity ℝ (0 + (k + 1)) 0 -
    P5L1Variation.cellDensity ℝ (0 + k) 0 = _
  simp only [Nat.zero_add]
  rw [dyadicHaar_eq_support]
  simpa only [Nat.mul_zero, leftDyadicIndex] using
    P5L1Variation.cellDensity_left_difference ℝ k 0

theorem leftLeafTest_mean_zero (N : ℕ) :
    probabilityLpMean (𝕜 := ℝ) (leftLeafTest N) = 0 := by
  rw [leftLeafTest_eq_sum, map_sum]
  simp only [map_smul, dyadicHaar_mean_zero, smul_zero, Finset.sum_const_zero]

theorem leftDyadicHaar_on_annulus (k j : ℕ) :
    ∀ᵐ x ∂unitIntervalMeasure, x ∈ leftDyadicBranch.annulus j →
      dyadicHaar ℝ 1 (leftDyadicIndex k) x =
        if k < j then 1 else if k = j then -1 else 0 := by
  have he : (2 : ℝ) ^ k • dyadicHaar ℝ 1 (leftDyadicIndex k) =
      leftDyadicBranch.density ℝ (k + 1) - leftDyadicBranch.density ℝ k := by
    change _ = P5L1Variation.cellDensity ℝ (0 + (k + 1)) 0 -
      P5L1Variation.cellDensity ℝ (0 + k) 0
    simp only [Nat.zero_add]
    rw [dyadicHaar_eq_support]
    simpa only [Nat.mul_zero, leftDyadicIndex] using
      (P5L1Variation.cellDensity_left_difference ℝ k 0).symm
  filter_upwards [Lp.coeFn_smul ((2 : ℝ) ^ k) (dyadicHaar ℝ 1 (leftDyadicIndex k)),
    Lp.coeFn_sub (leftDyadicBranch.density ℝ (k + 1)) (leftDyadicBranch.density ℝ k),
    leftDyadicBranch.density_on_annulus ℝ (k + 1) j,
    leftDyadicBranch.density_on_annulus ℝ k j] with x hmul hsub hnext hcurrent hx
  have hvalues := congrArg (fun f : Lp ℝ 1 unitIntervalMeasure => f x) he
  dsimp only at hvalues
  rw [hmul, hsub] at hvalues
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hvalues
  change x ∈ leftDyadicBranch.annulus j →
    (leftDyadicBranch.density ℝ (k + 1)) x =
      if k + 1 ≤ j then (2 : ℝ) ^ (0 + (k + 1)) else 0 at hnext
  change x ∈ leftDyadicBranch.annulus j →
    (leftDyadicBranch.density ℝ k) x =
      if k ≤ j then (2 : ℝ) ^ (0 + k) else 0 at hcurrent
  rw [hnext hx, hcurrent hx] at hvalues
  simp only [Nat.zero_add] at hvalues
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  by_cases hkj : k < j
  · rw [if_pos hkj]
    rw [if_pos (by omega), if_pos hkj.le, pow_succ] at hvalues
    nlinarith
  · rw [if_neg hkj]
    by_cases hkeq : k = j
    · rw [if_pos hkeq]
      rw [if_neg (by omega), if_pos (by omega)] at hvalues
      nlinarith
    · rw [if_neg hkeq]
      rw [if_neg (by omega), if_neg (by omega)] at hvalues
      nlinarith

theorem l1SetReader_leftDyadicHaar (k j : ℕ) :
    l1SetReader (leftDyadicBranch.annulus j) (dyadicHaar ℝ 1 (leftDyadicIndex k)) =
      unitIntervalMeasure.real (leftDyadicBranch.annulus j) *
        (if k < j then 1 else if k = j then -1 else 0) := by
  rw [l1SetReader_apply]
  have he : (fun x => dyadicHaar ℝ 1 (leftDyadicIndex k) x) =ᵐ[
      unitIntervalMeasure.restrict (leftDyadicBranch.annulus j)]
        fun _ => if k < j then (1 : ℝ) else if k = j then -1 else 0 := by
    filter_upwards [ae_restrict_of_ae (leftDyadicHaar_on_annulus k j),
      ae_restrict_mem (leftDyadicBranch.annulus_measurable j)] with x hvalue hx
    exact hvalue hx
  rw [integral_congr_ae he, integral_const, measureReal_restrict_apply_univ]
  rfl

end SurveyStatements.P5
