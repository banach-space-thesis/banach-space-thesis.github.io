import ThesisCommon.Analysis.ContinuousMapPrincipalBandMeasure
import ThesisCommon.Analysis.ContinuousMapRieszUniqueness
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-! The actual signed measure of a real L1 density agrees with the signed
Riesz measure of its integration functional. In particular, continuous test
functions determine L1 densities on compact spaces with outer approximation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]
variable (μ : Measure K) [IsFiniteMeasure μ]

def realL1DensityMeasure (f : Lp ℝ 1 μ) : Measure K :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

instance realL1DensityMeasure_finite (f : Lp ℝ 1 μ) :
    IsFiniteMeasure (realL1DensityMeasure μ f) :=
  isFiniteMeasure_withDensity_ofReal (L1.integrable_coeFn f).2

omit [HasOuterApproxClosed K] in
theorem continuousMapL1Density_eq_integral_of_nonneg (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    continuousMapL1Density (𝕜 := ℝ) μ f = continuousMapIntegralCLM (realL1DensityMeasure μ f) := by
  ext g
  rw [continuousMapL1Density_apply]
  change (∫ x, f x * g x ∂μ) = ∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))
  rw [integral_withDensity_eq_integral_toReal_smul
    (Lp.stronglyMeasurable f).measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

theorem positiveContinuousMapRiesz_L1Density (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    positiveContinuousMapRiesz (continuousMapL1Density (𝕜 := ℝ) μ f)
      (continuousMapL1Density_nonneg μ f hf) = realL1DensityMeasure μ f := by
  have h := positiveContinuousMapRiesz_integral (realL1DensityMeasure μ f)
  simpa only [← continuousMapL1Density_eq_integral_of_nonneg μ f hf] using h

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] [BorelSpace K]
  [HasOuterApproxClosed K] [IsFiniteMeasure μ] in
theorem realL1_withDensity_signed_of_nonneg (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    μ.withDensityᵥ (f : K → ℝ) = (realL1DensityMeasure μ f).toSignedMeasure := by
  have he : (f : K → ℝ) =ᵐ[μ] fun x => (ENNReal.ofReal (f x)).toReal := by
    filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with x hx
    exact (ENNReal.toReal_ofReal hx).symm
  rw [WithDensityᵥEq.congr_ae he]
  apply withDensityᵥ_toReal (Lp.stronglyMeasurable f).measurable.ennreal_ofReal.aemeasurable
  have hfin := measure_ne_top (realL1DensityMeasure μ f) univ
  simpa only [realL1DensityMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ] using hfin

theorem continuousMapRieszSigned_L1Density_nonneg (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    continuousMapRieszSigned (continuousMapL1Density (𝕜 := ℝ) μ f) =
      μ.withDensityᵥ (f : K → ℝ) := by
  rw [realL1_withDensity_signed_of_nonneg μ f hf]
  have h := continuousMapRieszSigned_unique (continuousMapL1Density (𝕜 := ℝ) μ f)
    (realL1DensityMeasure μ f) 0 (fun g => by
      rw [continuousMapL1Density_eq_integral_of_nonneg μ f hf]
      simp [continuousMapIntegralCLM])
  simpa only [Measure.toSignedMeasure_zero, sub_zero] using h

theorem continuousMapRieszSigned_L1Density (f : Lp ℝ 1 μ) :
    continuousMapRieszSigned (continuousMapL1Density (𝕜 := ℝ) μ f) =
      μ.withDensityᵥ (f : K → ℝ) := by
  calc
    _ = continuousMapRieszSigned (continuousMapL1Density (𝕜 := ℝ) μ f⁺) -
        continuousMapRieszSigned (continuousMapL1Density (𝕜 := ℝ) μ f⁻) := by
      rw [← continuousMapRieszSigned_sub, ← map_sub, posPart_sub_negPart]
    _ = μ.withDensityᵥ ((f⁺ : Lp ℝ 1 μ) : K → ℝ) -
        μ.withDensityᵥ ((f⁻ : Lp ℝ 1 μ) : K → ℝ) := by
      rw [continuousMapRieszSigned_L1Density_nonneg μ _ (posPart_nonneg f),
        continuousMapRieszSigned_L1Density_nonneg μ _ (negPart_nonneg f)]
    _ = μ.withDensityᵥ (fun x => f⁺ x - f⁻ x) :=
      (withDensityᵥ_sub' (L1.integrable_coeFn f⁺) (L1.integrable_coeFn f⁻)).symm
    _ = _ := by
      apply WithDensityᵥEq.congr_ae
      have h := Lp.coeFn_sub f⁺ f⁻
      rw [posPart_sub_negPart] at h
      exact h.symm

theorem continuousMapL1Density_injective :
    Function.Injective (continuousMapL1Density (𝕜 := ℝ) μ) := by
  intro f g hfg
  apply Lp.ext
  apply (L1.integrable_coeFn f).ae_eq_of_withDensityᵥ_eq (L1.integrable_coeFn g)
  rw [← continuousMapRieszSigned_L1Density, ← continuousMapRieszSigned_L1Density, hfg]

end ThesisCommon
