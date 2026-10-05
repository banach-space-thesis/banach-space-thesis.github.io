import ThesisCommon.Analysis.IntegralOperatorMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! A dominated first marginal gives the column bound required to construct
an actual integral operator from a nonnegative integrable product density. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

theorem hasKernelBound_of_kernelMeasure_fst_le {k : X × Y → ℝ} {C : ℝ}
    (hki : Integrable k (μ.prod ν)) (hpos : ∀ z, 0 ≤ k z) (hC : 0 ≤ C)
    (hbound : (integralKernelMeasure μ ν k).map Prod.fst ≤ ENNReal.ofReal C • μ) :
    HasKernelBound μ ν k C := by
  have hcol : Integrable (fun x => ∫ y, k (x, y) ∂ν) μ := hki.integral_prod_left
  have hle : (fun x => ∫ y, k (x, y) ∂ν) ≤ᵐ[μ] fun _ => C := by
    apply ae_le_of_forall_setIntegral_le hcol (integrable_const C)
    intro a ha _
    have hpre : Prod.fst ⁻¹' a = a ×ˢ (univ : Set Y) := by ext z; simp
    have hval : ((integralKernelMeasure μ ν k).map Prod.fst a).toReal =
        ∫ x in a, ∫ y, k (x, y) ∂ν ∂μ := by
      rw [Measure.map_apply measurable_fst ha, hpre, integralKernelMeasure,
        withDensity_apply _ (ha.prod MeasurableSet.univ),
        ← ofReal_integral_eq_lintegral_ofReal hki.integrableOn
          (Eventually.of_forall hpos),
        ENNReal.toReal_ofReal (integral_nonneg hpos),
        setIntegral_prod k hki.integrableOn, Measure.restrict_univ]
    calc
      (∫ x in a, ∫ y, k (x, y) ∂ν ∂μ) =
          ((integralKernelMeasure μ ν k).map Prod.fst a).toReal := hval.symm
      _ ≤ ((ENNReal.ofReal C • μ) a).toReal :=
        ENNReal.toReal_mono (by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ a)) (hbound a)
      _ = ∫ _ in a, C ∂μ := by
        rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
          setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
  filter_upwards [hki.prod_right_ae, hle] with x hix hx
  refine ⟨hix, ?_⟩
  simpa only [Real.norm_of_nonneg (hpos _)] using hx

omit [IsFiniteMeasure μ] [SFinite ν] in
theorem exists_real_density_acPart (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] :
    ∃ k : X × Y → ℝ, Measurable k ∧ (∀ z, 0 ≤ k z) ∧ Integrable k (μ.prod ν) ∧
      integralKernelMeasure μ ν k = (μ.prod ν).withDensity (ρ.rnDeriv (μ.prod ν)) := by
  let k : X × Y → ℝ := fun z => (ρ.rnDeriv (μ.prod ν) z).toReal
  refine ⟨k, (Measure.measurable_rnDeriv ρ (μ.prod ν)).ennreal_toReal,
    (fun _ => ENNReal.toReal_nonneg), ?_, ?_⟩
  · exact integrable_toReal_of_lintegral_ne_top
      (Measure.measurable_rnDeriv ρ (μ.prod ν)).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top ρ (μ.prod ν)).ne
  · apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_ne_top ρ (μ.prod ν)] with z hz
    exact ENNReal.ofReal_toReal hz

end ThesisCommon
