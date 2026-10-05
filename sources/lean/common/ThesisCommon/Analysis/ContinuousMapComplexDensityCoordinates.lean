import ThesisCommon.Analysis.ContinuousMapPrincipalL1Equiv
import ThesisCommon.Analysis.ContinuousMapDualCoordinates
import ThesisCommon.Analysis.ComplexL1Coordinates

/-! Integration against actual complex L1 densities commutes with the
canonical real and imaginary coordinates of the continuous-map dual. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [IsFiniteMeasure μ]

theorem continuousMapL1Density_ofReal (f : Lp ℝ 1 μ) :
    continuousMapL1Density (𝕜 := ℂ) μ (complexL1OfReal μ f) =
      continuousMapDualOfReal (continuousMapL1Density (𝕜 := ℝ) μ f) := by
  apply continuousMap_complex_dual_ext
  intro g
  change _ = continuousMapDualComplexify _ (continuousMapOfReal g)
  rw [continuousMapDualComplexify_ofReal, continuousMapL1Density_apply,
    continuousMapL1Density_apply, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [complexL1OfReal_coe f] with x hx
  change complexL1OfReal μ f x * (g x : ℂ) = ((f x * g x : ℝ) : ℂ)
  rw [hx, Complex.ofReal_mul]

theorem continuousMapDualRe_L1Density (f : Lp ℂ 1 μ) :
    continuousMapDualRe (continuousMapL1Density (𝕜 := ℂ) μ f) =
      continuousMapL1Density (𝕜 := ℝ) μ (complexL1Re μ f) := by
  conv_lhs => rw [← complexL1_decomposition f]
  rw [map_add, map_smul, continuousMapL1Density_ofReal, continuousMapL1Density_ofReal,
    map_add, continuousMapDualRe_ofReal, continuousMapDualRe_smul,
    continuousMapDualRe_ofReal, continuousMapDualIm_ofReal]
  simp

theorem continuousMapDualIm_L1Density (f : Lp ℂ 1 μ) :
    continuousMapDualIm (continuousMapL1Density (𝕜 := ℂ) μ f) =
      continuousMapL1Density (𝕜 := ℝ) μ (complexL1Im μ f) := by
  conv_lhs => rw [← complexL1_decomposition f]
  rw [map_add, map_smul, continuousMapL1Density_ofReal, continuousMapL1Density_ofReal,
    map_add, continuousMapDualIm_ofReal, continuousMapDualIm_smul,
    continuousMapDualIm_ofReal, continuousMapDualRe_ofReal]
  simp

end ThesisCommon
