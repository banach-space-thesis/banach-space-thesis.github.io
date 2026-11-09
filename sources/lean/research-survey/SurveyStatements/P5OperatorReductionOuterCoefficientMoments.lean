import SurveyStatements.P5OperatorReductionInnerMatrixRestrictions
import SurveyStatements.P5OperatorReductionPacketMatrixDecay
import SurveyStatements.P5Support.LpHaarBackwardSelection
import SurveyStatements.P5Support.HaarSignSecondMoment

/-! Actual weighted Haar coefficients have bounded total variation and
uniformly vanishing random-sign second moments on bounded Lp families. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

local instance outerCoefficientNativeIntervalProbability :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

def operatorReductionOuterWeightedCoefficient (p : BanachExponent) (n : ℕ)
    (k : Fin (2 ^ n)) (y : IntervalLp 𝕜 p) : 𝕜 :=
  (intervalLpDyadicRadius n : 𝕜) * lpHaarDyadicCoefficient 𝕜 p n k y

theorem operatorReductionOuterWeightedCoefficient_eq_L1_coordinate
    (p : BanachExponent) (n : ℕ) (k : Fin (2 ^ n)) (y : IntervalLp 𝕜 p) :
    operatorReductionOuterWeightedCoefficient p n k y =
      lpHaarNormalizedCoordinate 𝕜 operatorReductionL1Exponent (some ⟨n, k⟩)
        (lebesgueLpToOne y) := by
  symm
  rw [lpHaarNormalizedCoordinate, ContinuousLinearMap.smul_apply, smul_eq_mul,
    lpHaarRawVector, lpHaarRawCoordinate,
    lpHaarDyadic_norm 𝕜 operatorReductionL1Exponent
      (by norm_num [operatorReductionL1Exponent]) n k k.isLt]
  simp only [operatorReductionL1Exponent, ENNReal.toReal_one, div_one, Real.rpow_one]
  rw [lebesgueLpToOne_HaarCoefficient 𝕜 p n k k.isLt y]
  rfl

theorem operatorReductionOuterWeightedCoefficient_sum_norm_le
    (p : BanachExponent) (n : ℕ) (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) :
    (∑ k ∈ S, ‖operatorReductionOuterWeightedCoefficient p n k y‖) ≤ ‖y‖ := by
  simp_rw [operatorReductionOuterWeightedCoefficient_eq_L1_coordinate]
  exact (innerMatrixNormalizedCoordinate_sum_le n S (lebesgueLpToOne y)).trans
    (lebesgueLpToOneValue_norm_le y)

theorem operatorReductionOuterWeightedCoefficient_eq_normalized
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ) (k : Fin (2 ^ n))
    (y : IntervalLp 𝕜 p) :
    operatorReductionOuterWeightedCoefficient p n k y =
      (((intervalLpDyadicRadius n) ^ (1 - 1 / p.val.toReal) : ℝ) : 𝕜) *
        lpHaarNormalizedCoordinate 𝕜 p (some ⟨n, k⟩) y := by
  rw [operatorReductionOuterWeightedCoefficient, lpHaarNormalizedCoordinate,
    ContinuousLinearMap.smul_apply, smul_eq_mul, lpHaarRawVector, lpHaarRawCoordinate,
    lpHaarDyadic_norm 𝕜 p hp n k k.isLt]
  rw [← mul_assoc, ← RCLike.ofReal_mul,
    ← Real.rpow_add (intervalLpDyadicRadius_pos n), sub_add_cancel, Real.rpow_one]

theorem operatorReductionOuterWeightedCoefficient_norm_le
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ) (k : Fin (2 ^ n))
    (y : IntervalLp 𝕜 p) :
    ‖operatorReductionOuterWeightedCoefficient p n k y‖ ≤
      6 * ‖y‖ * (intervalLpDyadicRadius n) ^ (1 - 1 / p.val.toReal) := by
  rw [operatorReductionOuterWeightedCoefficient_eq_normalized p hp n k y,
    norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg (Real.rpow_nonneg (intervalLpDyadicRadius_pos n).le _)]
  have hcoord : ‖lpHaarNormalizedCoordinate 𝕜 p (some ⟨n, k⟩) y‖ ≤ 6 * ‖y‖ :=
    ((lpHaarNormalizedCoordinate 𝕜 p (some ⟨n, k⟩)).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right
        (packetMatrix_normalizedCoordinate_norm_le p hp (some ⟨n, k⟩)) (norm_nonneg y))
  calc
    _ ≤ (intervalLpDyadicRadius n) ^ (1 - 1 / p.val.toReal) * (6 * ‖y‖) :=
      mul_le_mul_of_nonneg_left hcoord
        (Real.rpow_nonneg (intervalLpDyadicRadius_pos n).le _)
    _ = _ := by ring

def operatorReductionOuterCoefficientSignForm (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) (θ : Fin S.card → Bool) : 𝕜 :=
  ∑ i, signedValue (θ i)
    (operatorReductionOuterWeightedCoefficient p n (S.orderEmbOfFin rfl i) y)

def operatorReductionOuterCoefficientVariance (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) : ℝ :=
  mean (fun θ : Fin S.card → Bool => ‖operatorReductionOuterCoefficientSignForm p n S y θ‖ ^ 2)

theorem operatorReductionOuterCoefficientSignForm_eq_block_sum (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) (θ : Fin (2 ^ n) → Bool) :
    operatorReductionOuterCoefficientSignForm p n S y (fun i => θ (S.orderEmbOfFin rfl i)) =
      ∑ k ∈ S, signedValue (θ k) (operatorReductionOuterWeightedCoefficient p n k y) :=
  packetMatrix_sum_index n S (fun k =>
    signedValue (θ k) (operatorReductionOuterWeightedCoefficient p n k y))

theorem operatorReductionOuterCoefficientVariance_eq_sum (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) :
    operatorReductionOuterCoefficientVariance p n S y =
      ∑ i : Fin S.card,
        ‖operatorReductionOuterWeightedCoefficient p n (S.orderEmbOfFin rfl i) y‖ ^ 2 :=
  haar_sign_second_moment _

theorem operatorReductionOuterCoefficientVariance_nonneg (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) :
    0 ≤ operatorReductionOuterCoefficientVariance p n S y :=
  mean_nonneg (fun _ => sq_nonneg _)

theorem operatorReductionOuterCoefficient_variance_le (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) :
    operatorReductionOuterCoefficientVariance p n S y ≤
      6 * ‖y‖ ^ 2 * (intervalLpDyadicRadius n) ^ (1 - 1 / p.val.toReal) := by
  rw [operatorReductionOuterCoefficientVariance_eq_sum]
  have hsum : (∑ i : Fin S.card,
      ‖operatorReductionOuterWeightedCoefficient p n (S.orderEmbOfFin rfl i) y‖) ≤ ‖y‖ := by
    rw [packetMatrix_sum_index n S (fun k =>
      ‖operatorReductionOuterWeightedCoefficient p n k y‖)]
    exact operatorReductionOuterWeightedCoefficient_sum_norm_le p n S y
  calc
    _ ≤ (6 * ‖y‖ * (intervalLpDyadicRadius n) ^ (1 - 1 / p.val.toReal)) * ‖y‖ :=
      haar_sign_variance_le _
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (norm_nonneg y))
          (Real.rpow_nonneg (intervalLpDyadicRadius_pos n).le _))
        (fun i => operatorReductionOuterWeightedCoefficient_norm_le p hp n _ y) hsum
    _ = _ := by ring

theorem operatorReductionOuterCoefficient_variance_le_norm_bound
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (y : IntervalLp 𝕜 p) (C : ℝ) (hy : ‖y‖ ≤ C) :
    operatorReductionOuterCoefficientVariance p n S y ≤
      6 * C ^ 2 * (intervalLpDyadicRadius n) ^ (1 - 1 / p.val.toReal) := by
  have hC : 0 ≤ C := (norm_nonneg y).trans hy
  have hsq : ‖y‖ ^ 2 ≤ C ^ 2 := (sq_le_sq₀ (norm_nonneg y) hC).mpr hy
  exact (operatorReductionOuterCoefficient_variance_le p hp n S y).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 6))
      (Real.rpow_nonneg (intervalLpDyadicRadius_pos n).le _))

theorem operatorReductionOuterCoefficient_variance_bound_tendsto_zero
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val) (C : ℝ) :
    Tendsto (fun n : ℕ =>
      6 * C ^ 2 * (intervalLpDyadicRadius n) ^ (1 - 1 / p.val.toReal)) atTop (𝓝 0) := by
  have hpReal : 1 < p.val.toReal := packetMatrix_one_lt_toReal p hp hp1
  have hα : 0 < 1 - 1 / p.val.toReal := sub_pos.mpr
    ((div_lt_iff₀ (show 0 < p.val.toReal by linarith)).mpr (by simpa using hpReal))
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (1 - 1 / p.val.toReal) := by positivity
  have hq1 : (1 / 2 : ℝ) ^ (1 - 1 / p.val.toReal) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  simpa only [intervalLpDyadicRadius,
    Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_zero] using
    h.const_mul (6 * C ^ 2)

/-- This threshold is independent of the packet and of the particular
bounded function, permitting bounded depth-dependent scalar slices. -/
theorem operatorReductionOuterCoefficient_variance_uniform_small
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ S : Finset (Fin (2 ^ n)), ∀ y : IntervalLp 𝕜 p,
      ‖y‖ ≤ C → operatorReductionOuterCoefficientVariance p n S y < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((operatorReductionOuterCoefficient_variance_bound_tendsto_zero p hp hp1 C).eventually
      (gt_mem_nhds hε))
  exact ⟨N, fun n hn S y hy =>
    (operatorReductionOuterCoefficient_variance_le_norm_bound p hp n S y C hy).trans_lt
      (hN n hn)⟩

theorem operatorReductionOuterCoefficient_family_sum_uniform_small
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (C : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ S : Finset (Fin (2 ^ n)),
      ∀ y : Fin r → IntervalLp 𝕜 p, (∀ i, ‖y i‖ ≤ C) →
      (∑ i, operatorReductionOuterCoefficientVariance p n S (y i)) < ε ^ 2 := by
  let δ : ℝ := ε ^ 2 / ((r : ℝ) + 1)
  have hden : 0 < (r : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) hden
  obtain ⟨N, hN⟩ := operatorReductionOuterCoefficient_variance_uniform_small
    (𝕜 := 𝕜) p hp hp1 C hδ
  refine ⟨N, ?_⟩
  intro n hn S y hy
  calc
    _ ≤ ∑ _i : Fin r, δ := Finset.sum_le_sum (fun i _ => (hN n hn S (y i) (hy i)).le)
    _ = (r : ℝ) * δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ((r : ℝ) + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε ^ 2 := by dsimp [δ]; field_simp [hden.ne']

end SurveyStatements.P5OperatorReduction
