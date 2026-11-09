import SurveyStatements.P5CaponRingReaders

/-! Actual left-descending leaf tests in any inner dyadic root cell.
Scaling the normalized densities by the root measure retains the patch area. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open P5Support P5L1Variation

def caponLocalBranch (m : ℕ) (root : Fin (2 ^ m)) : DyadicBranch m where
  index j := ⟨root.val * 2 ^ j, by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right root.isLt (by positivity)⟩
  parent j := by
    apply Fin.ext
    change (root.val * 2 ^ (j + 1)) / 2 = root.val * 2 ^ j
    rw [pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel]
    norm_num

def caponLocalInnerIndex (m : ℕ) (root : Fin (2 ^ m)) (k : ℕ) : DyadicIndex :=
  ⟨m + k, (caponLocalBranch m root).index k⟩

def caponLocalLeaf (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) : Lp ℝ 1 unitIntervalMeasure :=
  intervalLpDyadicRadius m • (caponLocalBranch m root).leafTest ℝ N

theorem caponLocalInnerIndex_contained (m : ℕ) (root : Fin (2 ^ m)) (k : ℕ) :
    lpHaarCell (m + k) ((caponLocalBranch m root).index k) ⊆ lpHaarCell m root := by
  have h := (caponLocalBranch m root).cell_antitone (Nat.zero_le k)
  simpa only [DyadicBranch.cell, caponLocalBranch, Nat.add_zero, pow_zero,
    Nat.mul_one, Fin.eta] using h

theorem norm_caponLocalLeaf_le (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) :
    ‖caponLocalLeaf m root N‖ ≤ 2 * intervalLpDyadicRadius m := by
  rw [caponLocalLeaf, norm_smul, Real.norm_eq_abs,
    abs_of_pos (intervalLpDyadicRadius_pos m)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    ((caponLocalBranch m root).leafTest_norm_le ℝ N) (intervalLpDyadicRadius_pos m).le

theorem caponLocalBranch_difference (m : ℕ) (root : Fin (2 ^ m)) (k : ℕ) :
    (caponLocalBranch m root).density ℝ (k + 1) -
      (caponLocalBranch m root).density ℝ k =
        (2 : ℝ) ^ (m + k) • dyadicHaar ℝ 1 (caponLocalInnerIndex m root k) := by
  rw [dyadicHaar_eq_support]
  change cellDensity ℝ (m + (k + 1)) (root.val * 2 ^ (k + 1)) -
    cellDensity ℝ (m + k) (root.val * 2 ^ k) = _
  rw [show m + (k + 1) = (m + k) + 1 by omega,
    show root.val * 2 ^ (k + 1) = 2 * (root.val * 2 ^ k) by rw [pow_succ]; ring]
  exact cellDensity_left_difference ℝ (m + k) (root.val * 2 ^ k)

theorem caponLocalLeaf_eq_sum (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) :
    caponLocalLeaf m root N = ∑ k ∈ Finset.range N,
      (2 : ℝ) ^ k • dyadicHaar ℝ 1 (caponLocalInnerIndex m root k) := by
  rw [caponLocalLeaf, DyadicBranch.leafTest_eq_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [caponLocalBranch_difference, smul_smul]
  congr 1
  rw [intervalLpDyadicRadius, pow_add, div_pow, one_pow]
  field_simp

theorem caponLocalLeaf_mean_zero (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) :
    probabilityLpMean (𝕜 := ℝ) (caponLocalLeaf m root N) = 0 := by
  rw [caponLocalLeaf_eq_sum, map_sum]
  simp only [map_smul, dyadicHaar_mean_zero, smul_zero, Finset.sum_const_zero]

theorem caponLocalInnerHaar_on_annulus (m : ℕ) (root : Fin (2 ^ m)) (k j : ℕ) :
    ∀ᵐ x ∂unitIntervalMeasure, x ∈ (caponLocalBranch m root).annulus j →
      dyadicHaar ℝ 1 (caponLocalInnerIndex m root k) x =
        if k < j then 1 else if k = j then -1 else 0 := by
  let B := caponLocalBranch m root
  have he : (2 : ℝ) ^ (m + k) • dyadicHaar ℝ 1 (caponLocalInnerIndex m root k) =
      B.density ℝ (k + 1) - B.density ℝ k := (caponLocalBranch_difference m root k).symm
  filter_upwards [Lp.coeFn_smul ((2 : ℝ) ^ (m + k))
    (dyadicHaar ℝ 1 (caponLocalInnerIndex m root k)),
    Lp.coeFn_sub (B.density ℝ (k + 1)) (B.density ℝ k),
    B.density_on_annulus ℝ (k + 1) j, B.density_on_annulus ℝ k j]
    with x hmul hsub hnext hcurrent hx
  have hvalues := congrArg (fun f : Lp ℝ 1 unitIntervalMeasure => f x) he
  dsimp only at hvalues
  rw [hmul, hsub] at hvalues
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hvalues
  change x ∈ B.annulus j → B.density ℝ (k + 1) x =
    if k + 1 ≤ j then (2 : ℝ) ^ (m + (k + 1)) else 0 at hnext
  change x ∈ B.annulus j → B.density ℝ k x =
    if k ≤ j then (2 : ℝ) ^ (m + k) else 0 at hcurrent
  rw [hnext hx, hcurrent hx] at hvalues
  have hpow : (0 : ℝ) < 2 ^ (m + k) := by positivity
  by_cases hkj : k < j
  · rw [if_pos hkj]
    rw [if_pos (by omega), if_pos hkj.le,
      show m + (k + 1) = (m + k) + 1 by omega, pow_succ] at hvalues
    nlinarith
  · rw [if_neg hkj]
    by_cases hkeq : k = j
    · rw [if_pos hkeq]
      rw [if_neg (by omega), if_pos (by omega)] at hvalues
      nlinarith
    · rw [if_neg hkeq]
      rw [if_neg (by omega), if_neg (by omega)] at hvalues
      nlinarith

theorem l1SetReader_caponLocalInnerHaar (m : ℕ) (root : Fin (2 ^ m)) (k j : ℕ) :
    l1SetReader ((caponLocalBranch m root).annulus j)
      (dyadicHaar ℝ 1 (caponLocalInnerIndex m root k)) =
        unitIntervalMeasure.real ((caponLocalBranch m root).annulus j) *
          (if k < j then 1 else if k = j then -1 else 0) := by
  rw [l1SetReader_apply]
  have he : (fun x => dyadicHaar ℝ 1 (caponLocalInnerIndex m root k) x) =ᵐ[
      unitIntervalMeasure.restrict ((caponLocalBranch m root).annulus j)]
        fun _ => if k < j then (1 : ℝ) else if k = j then -1 else 0 := by
    filter_upwards [ae_restrict_of_ae (caponLocalInnerHaar_on_annulus m root k j),
      ae_restrict_mem ((caponLocalBranch m root).annulus_measurable j)] with x hvalue hx
    exact hvalue hx
  rw [integral_congr_ae he, integral_const, measureReal_restrict_apply_univ]
  rfl

theorem caponLocal_ring_contribution_le (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ) :
    intervalLpDyadicRadius m / 4 ≤
      unitIntervalMeasure.real ((caponLocalBranch m root).annulus (n + 1)) *
        ((2 : ℝ) ^ (n + 1) - 1) := by
  have hm : unitIntervalMeasure.real ((caponLocalBranch m root).annulus (n + 1)) =
      intervalLpDyadicRadius m * unitIntervalMeasure.real (leftDyadicBranch.annulus (n + 1)) := by
    change (volume.restrict (Icc (0 : ℝ) 1)).real _ =
      intervalLpDyadicRadius m * (volume.restrict (Icc (0 : ℝ) 1)).real _
    rw [(caponLocalBranch m root).annulus_real_measure, leftDyadicBranch.annulus_real_measure]
    simp only [Nat.zero_add, intervalLpDyadicRadius, pow_add, one_div_pow]
    ring
  rw [hm]
  have h := mul_le_mul_of_nonneg_left (capon_ring_contribution_le n)
    (intervalLpDyadicRadius_pos m).le
  convert h using 1 <;> ring

end SurveyStatements.P5
