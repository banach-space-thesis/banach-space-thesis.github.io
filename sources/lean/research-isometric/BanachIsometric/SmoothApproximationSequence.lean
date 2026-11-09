import BanachIsometric.SmoothLipschitzApproximation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A concrete sequence of smooth approximations

The bumps have radii `1/(n+1)` and `2/(n+1)`. The approximating maps retain the
original global Lipschitz constant and have a uniform error bound tending to
zero. In particular this construction is available for the actual cone maps.
-/

namespace BanachIsometric

open MeasureTheory Metric Filter
open scoped Topology NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def shrinkingBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ContDiffBump (0 : E) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_right one_lt_two (by positivity)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem shrinkingBump_rOut_tendsto :
    Tendsto (fun n => (shrinkingBump E n).rOut) atTop (𝓝 0) := by
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  simpa only [shrinkingBump, mul_one_div, mul_zero] using ht

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem shrinkingBump_ratio (n : ℕ) :
    (shrinkingBump E n).rOut ≤ 2 * (shrinkingBump E n).rIn := by
  change 2 / ((n : ℝ) + 1) ≤ 2 * (1 / ((n : ℝ) + 1))
  rw [mul_one_div]

theorem exists_smooth_lipschitz_uniform_approximation
    (μ : Measure E) [μ.IsAddHaarMeasure] [CompleteSpace F]
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧ LipschitzWith C g ∧
      ∀ x, dist (g x) (f x) < ε := by
  let R : ℝ := ε / ((C : ℝ) + 1)
  have hC : 0 < (C : ℝ) + 1 := by positivity
  have hR : 0 < R := div_pos hε hC
  let φ : ContDiffBump (0 : E) := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  refine ⟨smoothBumpConvolution μ φ f, contDiff_smoothBumpConvolution μ φ hf,
    lipschitzWith_smoothBumpConvolution μ φ hf, fun x => ?_⟩
  apply (dist_smoothBumpConvolution_le μ φ hf x).trans_lt
  change (C : ℝ) * (ε / ((C : ℝ) + 1)) < ε
  calc
    (C : ℝ) * (ε / ((C : ℝ) + 1)) = ε * ((C : ℝ) / ((C : ℝ) + 1)) := by ring
    _ < ε * 1 := mul_lt_mul_of_pos_left ((div_lt_one hC).mpr (by linarith)) hε
    _ = ε := mul_one ε

end BanachIsometric
