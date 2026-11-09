import PL1.EnfloVanishing
import PL1.EnfloSum
import PL1.DyadicProjection

/-! Intrinsic weighted defects force dyadic maximum decay in every graph coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal NNReal

namespace PL1.EnfloBush
open IntrinsicGraph ResolventEstimates

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable (S : DyadicSystem ℝ (Lp ℝ 1 μ))

theorem norm_intrinsic_coord_le (n : ℕ) (x : S.IntrinsicSpace) :
    ‖coord S.analysis n x‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by simp) (x : IntrinsicGraph.Ambient (Y := Lp ℝ 1 μ)) n

theorem intrinsic_defect_eq (n : ℕ) (x : S.IntrinsicSpace) :
    evalZero S.analysis x - S.operator (n + 1) (evalZero S.analysis x) =
      dyadicRatio ^ (n + 1) • coord S.analysis (n + 1) x := by
  rw [coord_eq]
  change _ = dyadicRatio ^ (n + 1) •
    ((dyadicRatio ^ (n + 1))⁻¹ •
      (evalZero S.analysis x - S.operator (n + 1) (evalZero S.analysis x)))
  rw [smul_smul, mul_inv_cancel₀ (dyadicRatio_pow_ne_zero _), one_smul]

theorem norm_intrinsic_operator_approx_le
    (T : IntervalL1 ℝ →L[ℝ] S.IntrinsicSpace) (n : ℕ) :
    ‖(S.operator (n + 1)).comp ((evalZero S.analysis).comp T) -
      (evalZero S.analysis).comp T‖ ≤ dyadicRatio ^ (n + 1) * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (pow_nonneg dyadicRatio_nonneg _) (norm_nonneg T))
  intro f
  change ‖S.operator (n + 1) (evalZero S.analysis (T f)) - evalZero S.analysis (T f)‖ ≤ _
  rw [norm_sub_rev, intrinsic_defect_eq μ S n (T f), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg dyadicRatio_nonneg _)]
  calc
    _ ≤ dyadicRatio ^ (n + 1) * ‖T f‖ := mul_le_mul_of_nonneg_left
      (norm_intrinsic_coord_le μ S (n + 1) (T f)) (pow_nonneg dyadicRatio_nonneg _)
    _ ≤ dyadicRatio ^ (n + 1) * (‖T‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm f) (pow_nonneg dyadicRatio_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

variable (hS : ∀ n (A : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ),
  DyadicVanishing ((S.operator n).comp A))

include hS

theorem dyadicVanishing_intrinsic_evalZero (T : IntervalL1 ℝ →L[ℝ] S.IntrinsicSpace) :
    DyadicVanishing ((evalZero S.analysis).comp T) := by
  apply dyadicVanishing_of_opNorm_tendsto _
    (fun n => (S.operator (n + 1)).comp ((evalZero S.analysis).comp T))
  · intro n
    exact hS (n + 1) _
  · apply squeeze_zero (fun n => norm_nonneg _) (norm_intrinsic_operator_approx_le μ S T)
    have hp : Tendsto (fun n : ℕ => dyadicRatio ^ (n + 1)) atTop (𝓝 0) := by
      simpa only [pow_succ, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one dyadicRatio_nonneg dyadicRatio_lt_one).mul_const dyadicRatio
    simpa only [zero_mul] using hp.mul_const ‖T‖

theorem dyadicVanishing_intrinsic_coord (T : IntervalL1 ℝ →L[ℝ] S.IntrinsicSpace) (n : ℕ) :
    DyadicVanishing ((coord S.analysis n).comp T) := by
  have hzero := dyadicVanishing_intrinsic_evalZero μ S hS T
  cases n with
  | zero => exact hzero
  | succ n =>
    have he : (coord S.analysis (n + 1)).comp T =
        (dyadicRatio ^ (n + 1))⁻¹ •
          ((evalZero S.analysis).comp T -
            (S.operator (n + 1)).comp ((evalZero S.analysis).comp T)) := by
      ext1 f
      rw [ContinuousLinearMap.comp_apply, coord_eq]
      rfl
    rw [he]
    exact (hzero.sub (hS (n + 1) _)).smul _

variable [SFinite μ]

theorem dyadicVanishing_intrinsic_flatten (T : IntervalL1 ℝ →L[ℝ] S.IntrinsicSpace) :
    DyadicVanishing ((IntervalModel.flattenIsometry (𝕜 := ℝ) μ).toContinuousLinearMap.comp
      (S.inclusion.toContinuousLinearMap.comp T)) := by
  apply dyadicVanishing_flatten_of_coordinates
  intro n
  exact dyadicVanishing_intrinsic_coord μ S hS T n

theorem not_boundedBelow_intrinsic (T : IntervalL1 ℝ →L[ℝ] S.IntrinsicSpace)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ f, c * ‖f‖ ≤ ‖T f‖) : False := by
  apply not_boundedBelow_sum_of_coordinates μ (S.inclusion.toContinuousLinearMap.comp T)
    (fun n => dyadicVanishing_intrinsic_coord μ S hS T n) hc
  intro f
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map] using hlower f

end PL1.EnfloBush
