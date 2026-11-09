import PL1.EnfloMajorant
import PL1.DyadicCoordinateDomination
import PL1.IntervalModel

/-! Coordinatewise dyadic maximum decay excludes an L1 copy in a true ell1 sum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace PL1.EnfloBush
open IntervalModel DyadicTrace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

theorem maxMass_flatten (n : ℕ) (f : ℕ → L1Sum (Lp ℝ 1 μ)) :
    maxMass n (fun j => flatten μ (f j)) =
      ∑' i, maxMass n (fun j => f j i) := by
  have he : (fun z => maxAbs n (fun j => flatten μ (f j) z)) =ᵐ[disjointMeasure μ]
      (fun z : ℕ × Ω => maxAbs n (fun j => f j z.1 z.2)) := by
    filter_upwards [ae_all_iff.mpr (fun j => flatten_coeFn μ (f j))] with z hz
    exact maxAbs_congr (fun j _ => hz j)
  have hi : Integrable (fun z : ℕ × Ω => maxAbs n (fun j => f j z.1 z.2))
      (Measure.count.prod μ) := (integrable_maxAbs n (fun j => flatten μ (f j))).congr he
  rw [maxMass, integral_congr_ae he, disjointMeasure, integral_prod _ hi,
    integral_countable hi.integral_prod_left]
  simp [measureReal_def, maxMass]

def sumCoordinate (T : IntervalL1 ℝ →L[ℝ] L1Sum (Lp ℝ 1 μ)) (i : ℕ) :
    IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ :=
  (lp.evalCLM ℝ (fun _ : ℕ => Lp ℝ 1 μ) 1 i).comp T

omit [SFinite μ] in
theorem sumCoordinate_apply (T : IntervalL1 ℝ →L[ℝ] L1Sum (Lp ℝ 1 μ))
    (i : ℕ) (f : IntervalL1 ℝ) : sumCoordinate μ T i f = T f i := rfl

omit [SFinite μ] in
theorem sum_dyadicSumMass_le (T : IntervalL1 ℝ →L[ℝ] L1Sum (Lp ℝ 1 μ))
    (m : ℕ) (s : Finset ℕ) : ∑ i ∈ s, dyadicSumMass (sumCoordinate μ T i) m ≤ ‖T‖ := by
  classical
  simp only [dyadicSumMass, sumCoordinate_apply]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j ∈ Finset.range (2 ^ m), ‖T (dyadicVector (𝕜 := ℝ) m j)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [L1Sum.norm_eq_tsum]
      exact (L1Sum.summable_norm (T (dyadicVector m j))).sum_le_tsum s
        (fun i hi => norm_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (2 ^ m), ‖T‖ * ‖dyadicVector (𝕜 := ℝ) m j‖ :=
      Finset.sum_le_sum (fun j _ => T.le_opNorm _)
    _ = ‖T‖ := by rw [← Finset.mul_sum, EnfloBush.sum_norm_dyadicVector, mul_one]

theorem dyadicMaxMass_flatten (T : IntervalL1 ℝ →L[ℝ] L1Sum (Lp ℝ 1 μ)) (m : ℕ) :
    dyadicMaxMass ((flattenIsometry (𝕜 := ℝ) μ).toContinuousLinearMap.comp T) m =
      ∑' i, dyadicMaxMass (sumCoordinate μ T i) m :=
  maxMass_flatten μ (2 ^ m) (fun j => T (dyadicVector m j))

theorem dyadicVanishing_flatten_of_coordinates
    (T : IntervalL1 ℝ →L[ℝ] L1Sum (Lp ℝ 1 μ))
    (h : ∀ i, DyadicVanishing (sumCoordinate μ T i)) :
    DyadicVanishing ((flattenIsometry (𝕜 := ℝ) μ).toContinuousLinearMap.comp T) := by
  change Tendsto (fun m => dyadicMaxMass
    ((flattenIsometry (𝕜 := ℝ) μ).toContinuousLinearMap.comp T) m) atTop (𝓝 0)
  simp_rw [dyadicMaxMass_flatten]
  apply DyadicCoordinateDomination.tendsto_tsum_zero_of_increasing_majorants
    (fun m i => dyadicSumMass (sumCoordinate μ T i) m) _ ‖T‖
  · intro m i
    exact dyadicSumMass_nonneg _ _
  · intro i
    exact dyadicSumMass_monotone _
  · exact sum_dyadicSumMass_le μ T
  · intro m i
    exact dyadicMaxMass_nonneg _ _
  · intro m i
    exact dyadicMaxMass_le_sum _ _
  · exact h

theorem not_boundedBelow_sum_of_coordinates
    (T : IntervalL1 ℝ →L[ℝ] L1Sum (Lp ℝ 1 μ))
    (h : ∀ i, DyadicVanishing (sumCoordinate μ T i))
    {c : ℝ} (hc : 0 < c) (hlower : ∀ f, c * ‖f‖ ≤ ‖T f‖) : False := by
  apply not_boundedBelow_of_dyadicVanishing
    (dyadicVanishing_flatten_of_coordinates μ T h) hc
  intro f
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map] using hlower f

end PL1.EnfloBush
