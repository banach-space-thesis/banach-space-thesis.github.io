import ThesisCommon.Analysis.IntervalKernelBumps
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Lattice

/-! Jointly continuous nonnegative cutoffs converging to a moving punctured ball. -/
noncomputable section
open Filter Topology MeasureTheory
namespace ThesisCommon

def intervalPuncturedCutoff (r : ℝ) (n : ℕ) (t : UnitInterval) : C(UnitInterval, ℝ) :=
  ⟨fun x => min 1 ((n + 1 : ℝ) * dist t x) *
    min 1 ((n + 1 : ℝ) * max 0 (r - dist t x)), by fun_prop⟩

theorem intervalPuncturedCutoff_nonneg (r : ℝ) (n : ℕ) (t : UnitInterval) :
    0 ≤ intervalPuncturedCutoff r n t := by
  intro x
  change 0 ≤ min 1 ((n + 1 : ℝ) * dist t x) *
    min 1 ((n + 1 : ℝ) * max 0 (r - dist t x))
  positivity

theorem intervalPuncturedCutoff_le_one (r : ℝ) (n : ℕ) (t x : UnitInterval) :
    intervalPuncturedCutoff r n t x ≤ 1 := by
  change min 1 ((n + 1 : ℝ) * dist t x) *
    min 1 ((n + 1 : ℝ) * max 0 (r - dist t x)) ≤ 1
  exact mul_le_one₀ (min_le_left _ _) (by positivity) (min_le_left _ _)

theorem continuous_intervalPuncturedCutoff (r : ℝ) (n : ℕ) :
    Continuous (intervalPuncturedCutoff r n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun tx : UnitInterval × UnitInterval =>
    min 1 ((n + 1 : ℝ) * dist tx.1 tx.2) *
      min 1 ((n + 1 : ℝ) * max 0 (r - dist tx.1 tx.2)))
  fun_prop

theorem eventually_nat_succ_mul_ge_one {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (n + 1 : ℝ) * δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hN' := (div_lt_iff₀ hδ).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  nlinarith

theorem intervalPuncturedCutoff_tendsto (r : ℝ) (t x : UnitInterval) :
    Tendsto (fun n => intervalPuncturedCutoff r n t x) atTop
      (𝓝 ((Metric.ball t r \ {t}).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ Metric.ball t r \ {t}
  · rw [Set.indicator_of_mem hx]
    have hne : t ≠ x := fun h => hx.2 (Set.mem_singleton_iff.mpr h.symm)
    have hd : 0 < dist t x := dist_pos.mpr hne
    have hr : 0 < r - dist t x := by
      have h := hx.1
      rw [Metric.mem_ball, dist_comm] at h
      linarith
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_nat_succ_mul_ge_one hd, eventually_nat_succ_mul_ge_one hr]
      with n hn hn'
    symm
    change min 1 ((n + 1 : ℝ) * dist t x) *
      min 1 ((n + 1 : ℝ) * max 0 (r - dist t x)) = 1
    rw [max_eq_right hr.le, min_eq_left hn, min_eq_left hn', one_mul]
  · rw [Set.indicator_of_notMem hx]
    have hz (n : ℕ) : intervalPuncturedCutoff r n t x = 0 := by
      by_cases hxt : x = t
      · subst x
        simp [intervalPuncturedCutoff]
      · have hr : r ≤ dist t x := by
          have hxball : x ∉ Metric.ball t r := fun h => hx ⟨h, hxt⟩
          simpa only [Metric.mem_ball, not_lt, dist_comm] using hxball
        simp [intervalPuncturedCutoff, max_eq_left (sub_nonpos.mpr hr)]
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem integral_intervalPuncturedCutoff_tendsto (ν : Measure UnitInterval) [IsFiniteMeasure ν]
    (r : ℝ) (t : UnitInterval) :
    Tendsto (fun n => ∫ x, intervalPuncturedCutoff r n t x ∂ν) atTop
      (𝓝 (ν.real (Metric.ball t r \ {t}))) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (1 : ℝ))
    (fun n => (intervalPuncturedCutoff r n t).continuous.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall fun x => by
      exact (Real.norm_of_nonneg (show 0 ≤ intervalPuncturedCutoff r n t x from
        intervalPuncturedCutoff_nonneg r n t x)).le.trans (intervalPuncturedCutoff_le_one r n t x))
    (Eventually.of_forall (intervalPuncturedCutoff_tendsto r t))
  rw [integral_indicator (measurableSet_ball.diff (measurableSet_singleton t)), integral_const] at h
  simpa using h

end ThesisCommon
