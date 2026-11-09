import PL1.IntrinsicSpikeEstimates
import PL1.ConcreteResolvents

/-!
# The dyadic intrinsic spike norm and separation bounds

This file sums the actual resolvent commutator estimates with the intrinsic
coordinate weights. The remaining inputs explicitly concern multiplication
and head/tail independence in the genuine Haar L¹ space, over real or complex
scalars. No alternative intrinsic norm is introduced.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace PL1.IntrinsicSpikes
open Noise Walsh IntrinsicGraph ResolventEstimates IntrinsicSpikeEstimates

/-- The exact error coefficient in the manuscript's spike norm estimate. -/
def eta (T : PositiveTime) : ℝ := (2 / (T : ℝ)) * (dyadicRatio / (1 - dyadicRatio))

theorem eta_pos (T : PositiveTime) : 0 < eta T :=
  mul_pos (div_pos (by norm_num) T.property)
    (div_pos dyadicRatio_pos one_sub_dyadicRatio_pos)

theorem eta_eq (T : PositiveTime) : eta T = 2 / ((T : ℝ) * (Real.sqrt 2 - 1)) := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs1 : Real.sqrt 2 - 1 ≠ 0 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  unfold eta dyadicRatio
  field_simp

theorem exists_eta_lt {ε : ℝ} (hε : 0 < ε) : ∃ T : PositiveTime, eta T < ε := by
  let C : ℝ := 2 * (dyadicRatio / (1 - dyadicRatio))
  have hC : 0 < C := mul_pos (by norm_num)
    (div_pos dyadicRatio_pos one_sub_dyadicRatio_pos)
  let T : PositiveTime := ⟨C / ε + 1, by positivity⟩
  refine ⟨T, ?_⟩
  have heq : eta T = C / (T : ℝ) := by dsimp [eta, C]; ring
  rw [heq, div_lt_iff₀ T.property]
  have hc := div_mul_cancel₀ C hε.ne'
  change C < ε * (C / ε + 1)
  nlinarith

def error (T : PositiveTime) (b : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (2 / (T : ℝ)) * dyadicRatio ^ (n + 1) * b

theorem error_summable (T : PositiveTime) (b : ℝ) : Summable (error T b) :=
  (summable_nat_add_iff 1).mp
    ((geometric_tail_summable.mul_left (2 / (T : ℝ))).mul_right b)

theorem error_tsum (T : PositiveTime) (b : ℝ) : (∑' n, error T b n) = eta T * b := by
  rw [(error_summable T b).tsum_eq_zero_add]
  simp only [error, zero_add, tsum_mul_right, tsum_mul_left, geometric_tail_tsum, eta]

variable {𝕜 : Type*} [RCLike 𝕜]

theorem coordinate_commutator_le (rates : ℕ → ℝ≥0)
    (M : Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar)
    (f : (dyadicSystem 𝕜 rates).IntrinsicSpace) (T : PositiveTime)
    (hdefect : ∀ t : PositiveTime,
      ‖(M (evalZero (dyadicSystem 𝕜 rates).analysis f) -
          resolventL1 𝕜 rates t (M (evalZero (dyadicSystem 𝕜 rates).analysis f))) -
        M (evalZero (dyadicSystem 𝕜 rates).analysis f -
          resolventL1 𝕜 rates t (evalZero (dyadicSystem 𝕜 rates).analysis f))‖ ≤
        2 * (t : ℝ) / (T : ℝ) * ‖evalZero (dyadicSystem 𝕜 rates).analysis f‖) :
    ∀ n, ‖(dyadicSystem 𝕜 rates).analysis n
          (M (evalZero (dyadicSystem 𝕜 rates).analysis f)) -
        M (coord (dyadicSystem 𝕜 rates).analysis n f)‖ ≤
      error T ‖evalZero (dyadicSystem 𝕜 rates).analysis f‖ n := by
  intro n
  rw [coord_eq]
  cases n with
  | zero => simp [DyadicSystem.analysis, analysisCoordinate, error]
  | succ n =>
    simp only [DyadicSystem.analysis, analysisCoordinate,
      smul_apply, sub_apply,
      ContinuousLinearMap.id_apply, map_smul, ← smul_sub, norm_smul,
      RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg dyadicRatio_nonneg _))]
    have h := mul_le_mul_of_nonneg_left (hdefect (dyadicTime (n + 1)))
      (inv_nonneg.mpr (pow_nonneg dyadicRatio_nonneg (n + 1)))
    apply h.trans_eq
    have ht : (dyadicTime (n + 1) : ℝ) = (dyadicRatio ^ (n + 1)) ^ 2 := by
      dsimp [dyadicTime]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [ht]
    dsimp [error]
    field_simp

theorem exists_product (rates : ℕ → ℝ≥0)
    (M : Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar)
    (f : (dyadicSystem 𝕜 rates).IntrinsicSpace) (T : PositiveTime)
    (hpres : ∀ n, ‖M (coord (dyadicSystem 𝕜 rates).analysis n f)‖ =
      ‖coord (dyadicSystem 𝕜 rates).analysis n f‖)
    (hcomm : ∀ n, ‖(dyadicSystem 𝕜 rates).analysis n
          (M (evalZero (dyadicSystem 𝕜 rates).analysis f)) -
        M (coord (dyadicSystem 𝕜 rates).analysis n f)‖ ≤
      error T ‖evalZero (dyadicSystem 𝕜 rates).analysis f‖ n) :
    ∃ g : (dyadicSystem 𝕜 rates).IntrinsicSpace,
      evalZero (dyadicSystem 𝕜 rates).analysis g =
        M (evalZero (dyadicSystem 𝕜 rates).analysis f) ∧
      |‖g‖ - ‖f‖| ≤ eta T * ‖evalZero (dyadicSystem 𝕜 rates).analysis f‖ := by
  simpa only [error_tsum] using IntrinsicSpikeEstimates.exists_product rfl M f
    (error T ‖evalZero (dyadicSystem 𝕜 rates).analysis f‖)
    (error_summable T _) hpres hcomm

theorem separation (rates : ℕ → ℝ≥0)
    (M : Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar)
    (h f g : (dyadicSystem 𝕜 rates).IntrinsicSpace)
    (hg : evalZero (dyadicSystem 𝕜 rates).analysis g =
      M (evalZero (dyadicSystem 𝕜 rates).analysis f)) (T : PositiveTime) (δ : ℝ)
    (hsep : ∀ n, (1 - 2 * δ) *
        (‖coord (dyadicSystem 𝕜 rates).analysis n h‖ +
          ‖coord (dyadicSystem 𝕜 rates).analysis n f‖) ≤
      ‖coord (dyadicSystem 𝕜 rates).analysis n h +
        M (coord (dyadicSystem 𝕜 rates).analysis n f)‖)
    (hcomm : ∀ n, ‖(dyadicSystem 𝕜 rates).analysis n
          (M (evalZero (dyadicSystem 𝕜 rates).analysis f)) -
        M (coord (dyadicSystem 𝕜 rates).analysis n f)‖ ≤
      error T ‖evalZero (dyadicSystem 𝕜 rates).analysis f‖ n) :
    (1 - 2 * δ) * (‖h‖ + ‖f‖) -
      eta T * ‖evalZero (dyadicSystem 𝕜 rates).analysis f‖ ≤ ‖h + g‖ := by
  simpa only [error_tsum] using IntrinsicSpikeEstimates.separation M h f g hg
    (error T ‖evalZero (dyadicSystem 𝕜 rates).analysis f‖)
    (error_summable T _) (1 - 2 * δ) hsep hcomm

end PL1.IntrinsicSpikes
