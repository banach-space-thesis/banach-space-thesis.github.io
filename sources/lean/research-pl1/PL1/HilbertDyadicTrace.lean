import PL1.HilbertTraceBounds
import PL1.DyadicTrace

/-! # Dyadic trace decay from Hilbert smoothing on bounded inputs -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.HilbertDyadicTrace

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

abbrev cellVector (n i : ℕ) : Lp 𝕜 ∞ intervalMeasure :=
  TraceBounds.cellVector intervalMeasure (DyadicTrace.cell n)
    (DyadicTrace.measurableSet_cell n) i

theorem norm_trace_le (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (T : H →L[𝕜] IntervalL1 𝕜) (V : Lp 𝕜 ∞ intervalMeasure →L[𝕜] H)
    (hfactor : DyadicTrace.restrictLinfty R = T.comp V) (n : ℕ) :
    ‖DyadicTrace.trace n R‖ ≤ ‖T‖ *
      Real.sqrt (∑ i ∈ Finset.range (2 ^ n), ‖V (cellVector (𝕜 := 𝕜) n i)‖ ^ 2) := by
  change ‖TraceBounds.finiteTrace (Finset.range (2 ^ n)) (cellVector (𝕜 := 𝕜) n)
    (TraceBounds.cellFunctional (𝕜 := 𝕜) intervalMeasure (DyadicTrace.cell n)
      (DyadicTrace.measurableSet_cell n)) (DyadicTrace.restrictLinfty R)‖ ≤ _
  rw [hfactor]
  exact HilbertTraceBounds.norm_sum_cell_apply_le intervalMeasure (DyadicTrace.cell n)
    (DyadicTrace.measurableSet_cell n) (Finset.range (2 ^ n))
    (DyadicTrace.pairwiseDisjoint_cell n) T (fun i => V (cellVector (𝕜 := 𝕜) n i))

theorem trace_tendsto_zero_of_square_sum (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (T : H →L[𝕜] IntervalL1 𝕜) (V : Lp 𝕜 ∞ intervalMeasure →L[𝕜] H)
    (hfactor : DyadicTrace.restrictLinfty R = T.comp V)
    (hV : Tendsto (fun n => ∑ i ∈ Finset.range (2 ^ n),
      ‖V (cellVector (𝕜 := 𝕜) n i)‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => DyadicTrace.trace n R) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (norm_trace_le R T V hfactor)
  simpa using (hV.sqrt.const_mul ‖T‖)

omit [CompleteSpace H] in
theorem square_sum_le_geometric
    (V : Lp 𝕜 ∞ intervalMeasure →L[𝕜] H) (C q : ℝ) (_hC : 0 ≤ C) (_hq : 0 ≤ q)
    (hV : ∀ n i, i < 2 ^ n → ‖V (cellVector (𝕜 := 𝕜) n i)‖ ≤ C * q ^ n) (n : ℕ) :
    (∑ i ∈ Finset.range (2 ^ n), ‖V (cellVector (𝕜 := 𝕜) n i)‖ ^ 2) ≤
      C ^ 2 * (2 * q ^ 2) ^ n := by
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ n), (C * q ^ n) ^ 2 :=
      Finset.sum_le_sum (fun i hi =>
        pow_le_pow_left₀ (norm_nonneg _) (hV n i (Finset.mem_range.mp hi)) 2)
    _ = C ^ 2 * (2 * q ^ 2) ^ n := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
        mul_pow, ← pow_mul, mul_comm n 2]
      ring

theorem trace_tendsto_zero_of_geometric_bound (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (T : H →L[𝕜] IntervalL1 𝕜) (V : Lp 𝕜 ∞ intervalMeasure →L[𝕜] H)
    (hfactor : DyadicTrace.restrictLinfty R = T.comp V)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hdecay : 2 * q ^ 2 < 1)
    (hV : ∀ n i, i < 2 ^ n → ‖V (cellVector (𝕜 := 𝕜) n i)‖ ≤ C * q ^ n) :
    Tendsto (fun n => DyadicTrace.trace n R) atTop (𝓝 0) := by
  apply trace_tendsto_zero_of_square_sum R T V hfactor
  apply squeeze_zero (fun n => Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (square_sum_le_geometric V C q hC hq hV)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ 2 * q ^ 2 by positivity) hdecay).const_mul (C ^ 2)

theorem one_le_norm_id_sub_of_geometric_bound (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (T : H →L[𝕜] IntervalL1 𝕜) (V : Lp 𝕜 ∞ intervalMeasure →L[𝕜] H)
    (hfactor : DyadicTrace.restrictLinfty R = T.comp V)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hdecay : 2 * q ^ 2 < 1)
    (hV : ∀ n i, i < 2 ^ n → ‖V (cellVector (𝕜 := 𝕜) n i)‖ ≤ C * q ^ n) :
    1 ≤ ‖DyadicTrace.restrictLinfty (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) - R)‖ :=
  DyadicTrace.one_le_norm_id_sub R
    (trace_tendsto_zero_of_geometric_bound R T V hfactor C q hC hq hdecay hV)

theorem trace_tendsto_zero_of_power_bound (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (T : H →L[𝕜] IntervalL1 𝕜) (V : Lp 𝕜 ∞ intervalMeasure →L[𝕜] H)
    (hfactor : DyadicTrace.restrictLinfty R = T.comp V)
    (C r : ℝ) (hC : 0 ≤ C) (hr : 1 / 2 < r)
    (hV : ∀ n i, i < 2 ^ n →
      ‖V (cellVector (𝕜 := 𝕜) n i)‖ ≤ C * (((2 : ℝ) ^ n)⁻¹) ^ r) :
    Tendsto (fun n => DyadicTrace.trace n R) atTop (𝓝 0) := by
  have hq : 0 ≤ (2 : ℝ) ^ (-r) := Real.rpow_nonneg (by norm_num) _
  have hdecay : 2 * ((2 : ℝ) ^ (-r)) ^ 2 < 1 := by
    have heq : 2 * ((2 : ℝ) ^ (-r)) ^ 2 = (2 : ℝ) ^ (1 - 2 * r) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [Nat.cast_ofNat]
      rw [show -r * 2 = -(2 * r) by ring, Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      rw [Real.rpow_one, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rfl
    rw [heq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  apply trace_tendsto_zero_of_geometric_bound R T V hfactor C ((2 : ℝ) ^ (-r)) hC hq hdecay
  intro n i hi
  have heq : (((2 : ℝ) ^ n)⁻¹) ^ r = ((2 : ℝ) ^ (-r)) ^ n := by
    rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_comm (n : ℝ) (-r), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [heq] using hV n i hi

end PL1.HilbertDyadicTrace
