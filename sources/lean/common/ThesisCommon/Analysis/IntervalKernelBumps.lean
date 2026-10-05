import ThesisCommon.Analysis.IntervalKernelBounds
import Mathlib.Topology.CompactOpen

/-! Continuous moving test bumps for representing kernels. They are bounded
by one, equal one at their centre, and converge pointwise to the singleton
indicator. Applying an operator and evaluating at the moving centre remains
continuous. These are prerequisites for the measurable diagonal coefficient. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def intervalKernelBump (n : ℕ) (t : UnitInterval) : IntervalContinuous 𝕜 :=
  ⟨fun x => ((max 0 (1 - (n+1 : ℝ) * dist t x) : ℝ) : 𝕜), by fun_prop⟩

theorem intervalKernelBump_center (n : ℕ) (t : UnitInterval) :
    intervalKernelBump (𝕜 := 𝕜) n t t = 1 := by
  simp [intervalKernelBump]

theorem norm_intervalKernelBump_le (n : ℕ) (t : UnitInterval) :
    ‖intervalKernelBump (𝕜 := 𝕜) n t‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro x
  change ‖((max 0 (1 - (n+1 : ℝ) * dist t x) : ℝ) : 𝕜)‖ ≤ 1
  rw [RCLike.norm_ofReal, abs_of_nonneg (le_max_left _ _)]
  apply max_le zero_le_one
  have hp : 0 ≤ (n+1 : ℝ) * dist t x := mul_nonneg (by positivity) dist_nonneg
  linarith

theorem continuous_intervalKernelBump (n : ℕ) :
    Continuous (intervalKernelBump (𝕜 := 𝕜) n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun tx : UnitInterval × UnitInterval =>
    ((max 0 (1 - (n+1 : ℝ) * dist tx.1 tx.2) : ℝ) : 𝕜))
  fun_prop

theorem intervalKernelBump_eq_zero (n : ℕ) (t x : UnitInterval)
    (h : 1 ≤ (n+1 : ℝ) * dist t x) : intervalKernelBump (𝕜 := 𝕜) n t x = 0 := by
  change ((max 0 (1 - (n+1 : ℝ) * dist t x) : ℝ) : 𝕜) = 0
  rw [max_eq_left (by linarith)]
  simp

theorem intervalKernelBump_eventually_zero {t x : UnitInterval} (htx : t ≠ x) :
    ∀ᶠ n in atTop, intervalKernelBump (𝕜 := 𝕜) n t x = 0 := by
  have hd : 0 < dist t x := dist_pos.2 htx
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / dist t x)
  have hN' : 1 < (N : ℝ) * dist t x := (div_lt_iff₀ hd).1 hN
  filter_upwards [eventually_ge_atTop N] with n hn
  apply intervalKernelBump_eq_zero
  have hcast : (N : ℝ) ≤ n := Nat.cast_le.2 hn
  nlinarith

theorem intervalKernelBump_tendsto (t x : UnitInterval) :
    Tendsto (fun n => intervalKernelBump (𝕜 := 𝕜) n t x) atTop
      (𝓝 (if x = t then (1 : 𝕜) else 0)) := by
  by_cases h : x = t
  · subst x
    simpa only [intervalKernelBump_center, if_pos rfl] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 1))
  · rw [if_neg h]
    apply tendsto_const_nhds.congr'
    exact (intervalKernelBump_eventually_zero (𝕜 := 𝕜) (Ne.symm h)).mono (fun _ hn => hn.symm)

theorem continuous_intervalKernelBump_coefficient
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ) :
    Continuous (fun t => intervalOperatorKernel T t (intervalKernelBump n t)) := by
  change Continuous (fun t => T (intervalKernelBump n t) t)
  exact continuous_eval.comp ((T.continuous.comp (continuous_intervalKernelBump n)).prodMk continuous_id)

end ThesisCommon
