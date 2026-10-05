import ThesisCommon.Analysis.L1Lattice
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! The Radon--Nikodym density of a finite measure as an actual real L1
element, with positivity, additivity, and the mass norm for absolutely
continuous measures. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ThesisCommon
variable {Y : Type*} [MeasurableSpace Y]

theorem integrable_measureDensity (M ν : Measure Y) [IsFiniteMeasure M] :
    Integrable (fun y => (M.rnDeriv ν y).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv M ν).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top M ν).ne

def measureDensityL1 (M ν : Measure Y) [IsFiniteMeasure M] : Lp ℝ 1 ν :=
  (integrable_measureDensity M ν).toL1 (fun y => (M.rnDeriv ν y).toReal)

theorem measureDensityL1_coe (M ν : Measure Y) [IsFiniteMeasure M] :
    measureDensityL1 M ν =ᵐ[ν] fun y => (M.rnDeriv ν y).toReal :=
  Integrable.coeFn_toL1 _

theorem measureDensityL1_nonneg (M ν : Measure Y) [IsFiniteMeasure M] :
    0 ≤ measureDensityL1 M ν := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [measureDensityL1_coe M ν] with y hy
  rw [hy]
  exact ENNReal.toReal_nonneg

theorem measureDensityL1_setIntegral (M ν : Measure Y) [IsFiniteMeasure M] [SigmaFinite ν]
    (hAC : M ≪ ν) (s : Set Y) (hs : MeasurableSet s) :
    (∫ y in s, measureDensityL1 M ν y ∂ν) = (M s).toReal := by
  calc
    (∫ y in s, measureDensityL1 M ν y ∂ν) = ∫ y in s, (M.rnDeriv ν y).toReal ∂ν :=
      integral_congr_ae (ae_restrict_of_ae (measureDensityL1_coe M ν))
    _ = (M s).toReal := Measure.setIntegral_toReal_rnDeriv' hAC hs

theorem norm_measureDensityL1 (M ν : Measure Y) [IsFiniteMeasure M] [SigmaFinite ν]
    (hAC : M ≪ ν) : ‖measureDensityL1 M ν‖ = (M univ).toReal := by
  rw [measureDensityL1, L1.norm_of_fun_eq_integral_norm]
  simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact Measure.integral_toReal_rnDeriv hAC

theorem measureDensityL1_add (M N ν : Measure Y) [IsFiniteMeasure M] [IsFiniteMeasure N]
    [SigmaFinite ν] : measureDensityL1 (M + N) ν = measureDensityL1 M ν + measureDensityL1 N ν := by
  apply Lp.ext
  filter_upwards [measureDensityL1_coe (M + N) ν, measureDensityL1_coe M ν,
    measureDensityL1_coe N ν, Lp.coeFn_add (measureDensityL1 M ν) (measureDensityL1 N ν),
    Measure.rnDeriv_add M N ν, Measure.rnDeriv_ne_top M ν, Measure.rnDeriv_ne_top N ν]
      with y hsum hM hN hadd hrn hMt hNt
  rw [hsum, hadd, Pi.add_apply, hM, hN, hrn, Pi.add_apply, ENNReal.toReal_add hMt hNt]

/-- Equality of all finite-measure set integrals determines genuine L1
elements; this does not require any countable generator for the sigma-algebra. -/
theorem lOne_eq_of_setIntegrals_eq {ν : Measure Y} (f g : Lp ℝ 1 ν)
    (h : ∀ s, MeasurableSet s → ν s < ∞ → (∫ y in s, f y ∂ν) = ∫ y in s, g y ∂ν) : f = g := by
  apply Lp.ext
  exact Lp.ae_eq_of_forall_setIntegral_eq f g (by norm_num) (by norm_num)
    (fun _ _ _ => (L1.integrable_coeFn f).integrableOn)
    (fun _ _ _ => (L1.integrable_coeFn g).integrableOn) h

end ThesisCommon
