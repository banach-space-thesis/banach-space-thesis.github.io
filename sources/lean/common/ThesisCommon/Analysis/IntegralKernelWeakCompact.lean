import ThesisCommon.Analysis.HilbertWeakCompact
import ThesisCommon.Analysis.IntegralKernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Bounded measurable kernels factor through the actual Hilbert space L².
The weak compactness conclusion uses the weak topology and Banach--Alaoglu,
not a uniform-integrability or representation assumption. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]

def lTwoFiniteMeasureConstant (ν : Measure Y) : ℝ := (ν univ).toReal ^ (1 / 2 : ℝ)

omit [IsFiniteMeasure ν] in
theorem lTwoFiniteMeasureConstant_nonneg : 0 ≤ lTwoFiniteMeasureConstant ν :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

def lTwoToLOneFn (f : Lp ℝ 2 ν) : Lp ℝ 1 ν :=
  ((Lp.memLp f).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp f

theorem lTwoToLOneFn_coe (f : Lp ℝ 2 ν) : lTwoToLOneFn f =ᵐ[ν] f :=
  MemLp.coeFn_toLp _

theorem norm_lTwoToLOneFn_le (f : Lp ℝ 2 ν) :
    ‖lTwoToLOneFn f‖ ≤ lTwoFiniteMeasureConstant ν * ‖f‖ := by
  rw [lTwoToLOneFn, Lp.norm_toLp, lTwoFiniteMeasureConstant]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp f).1
  have hfin : eLpNorm f 2 ν * ν univ ^ (1 / (1 : ℝ≥0∞).toReal -
      1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    apply ENNReal.mul_ne_top (Lp.memLp f).2.ne
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact measure_ne_top ν univ
  have hreal := ENNReal.toReal_mono hfin h
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_self (one_ne_zero : (1 : ℝ) ≠ 0),
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hreal
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← Lp.norm_def] at hreal
  simpa only [mul_comm] using hreal

def lTwoToLOne (ν : Measure Y) [IsFiniteMeasure ν] : Lp ℝ 2 ν →L[ℝ] Lp ℝ 1 ν :=
  LinearMap.mkContinuous
    { toFun := lTwoToLOneFn
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [lTwoToLOneFn_coe (f + g), lTwoToLOneFn_coe f,
          lTwoToLOneFn_coe g, Lp.coeFn_add f g,
          Lp.coeFn_add (lTwoToLOneFn f) (lTwoToLOneFn g)] with y hfg hf hg ha hb
        simp only [hfg, hf, hg, ha, hb, Pi.add_apply]
      map_smul' := fun a f => by
        apply Lp.ext
        filter_upwards [lTwoToLOneFn_coe (a • f), lTwoToLOneFn_coe f,
          Lp.coeFn_smul a f, Lp.coeFn_smul a (lTwoToLOneFn f)] with y haf hf ha hb
        simp only [haf, hf, ha, hb, Pi.smul_apply, RingHom.id_apply] }
    (lTwoFiniteMeasureConstant ν) norm_lTwoToLOneFn_le

theorem norm_lTwoToLOne_le : ‖lTwoToLOne ν‖ ≤ lTwoFiniteMeasureConstant ν :=
  ContinuousLinearMap.opNorm_le_bound _ lTwoFiniteMeasureConstant_nonneg norm_lTwoToLOneFn_le

section Lift
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T : E →L[ℝ] Lp ℝ 1 ν) {C : ℝ}
variable (hbound : ∀ f, ∀ᵐ y ∂ν, ‖T f y‖ ≤ C * ‖f‖)

def boundedRangeLTwoFn (f : E) : Lp ℝ 2 ν :=
  (MemLp.of_bound (Lp.memLp (T f)).1 (C * ‖f‖) (hbound f)).toLp (T f)

theorem boundedRangeLTwoFn_coe (f : E) : boundedRangeLTwoFn T hbound f =ᵐ[ν] T f :=
  MemLp.coeFn_toLp _

theorem norm_boundedRangeLTwoFn_le (hC : 0 ≤ C) (f : E) :
    ‖boundedRangeLTwoFn T hbound f‖ ≤ (lTwoFiniteMeasureConstant ν * C) * ‖f‖ := by
  have hb : ∀ᵐ y ∂ν, ‖boundedRangeLTwoFn T hbound f y‖ ≤ C * ‖f‖ := by
    filter_upwards [boundedRangeLTwoFn_coe T hbound f, hbound f] with y hy hb
    rwa [hy]
  have h := Lp.norm_le_of_ae_bound (mul_nonneg hC (norm_nonneg f)) hb
  simpa only [lTwoFiniteMeasureConstant, measureUnivNNReal, mul_assoc,
    ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofNat, one_div] using h

def boundedRangeLTwo (hC : 0 ≤ C) : E →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := boundedRangeLTwoFn T hbound
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [boundedRangeLTwoFn_coe T hbound (f + g),
          boundedRangeLTwoFn_coe T hbound f, boundedRangeLTwoFn_coe T hbound g,
          Lp.coeFn_add (T f) (T g),
          Lp.coeFn_add (boundedRangeLTwoFn T hbound f) (boundedRangeLTwoFn T hbound g)]
          with y hfg hf hg ha hb
        simpa only [map_add, ha, hb, hf, hg, Pi.add_apply] using hfg
      map_smul' := fun a f => by
        apply Lp.ext
        filter_upwards [boundedRangeLTwoFn_coe T hbound (a • f),
          boundedRangeLTwoFn_coe T hbound f, Lp.coeFn_smul a (T f),
          Lp.coeFn_smul a (boundedRangeLTwoFn T hbound f)] with y haf hf ha hb
        simpa only [map_smul, ha, hb, hf, Pi.smul_apply, RingHom.id_apply] using haf }
    (lTwoFiniteMeasureConstant ν * C) (norm_boundedRangeLTwoFn_le T hbound hC)

theorem norm_boundedRangeLTwo_le (hC : 0 ≤ C) :
    ‖boundedRangeLTwo T hbound hC‖ ≤ lTwoFiniteMeasureConstant ν * C :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg lTwoFiniteMeasureConstant_nonneg hC) (norm_boundedRangeLTwoFn_le T hbound hC)

theorem lTwoToLOne_comp_boundedRangeLTwo (hC : 0 ≤ C) :
    (lTwoToLOne ν).comp (boundedRangeLTwo T hbound hC) = T := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (lTwoToLOneFn_coe _).trans (boundedRangeLTwoFn_coe T hbound f)

include hbound in
theorem weaklyCompact_of_bounded_range (hC : 0 ≤ C) : IsWeaklyCompactOperator T := by
  rw [← lTwoToLOne_comp_boundedRangeLTwo T hbound hC]
  exact weaklyCompact_of_hilbert_factorization _ _

end Lift

section Kernels
variable [SFinite μ] {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} {C : ℝ}

theorem IsIntegralKernel.apply_norm_le_of_bound (hk : IsIntegralKernel k K)
    (hbound : ∀ᵐ z ∂μ.prod ν, ‖k z‖ ≤ C) (f : Lp ℝ 1 μ) :
    ∀ᵐ y ∂ν, ‖K f y‖ ≤ C * ‖f‖ := by
  have hsections : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, ‖k (x, y)‖ ≤ C :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hbound)
  filter_upwards [hk.represents f, hk.integrable_section f, hsections] with y hy hi hb
  rw [hy]
  calc
    ‖∫ x, k (x, y) * f x ∂μ‖ ≤ ∫ x, ‖k (x, y) * f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * ‖f x‖ ∂μ := by
      apply integral_mono_ae hi.norm ((L1.integrable_coeFn f).norm.const_mul C)
      filter_upwards [hb] with x hx
      simpa only [norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))
    _ = C * ‖f‖ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm]

theorem IsIntegralKernel.weaklyCompact_of_bound (hk : IsIntegralKernel k K)
    (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂μ.prod ν, ‖k z‖ ≤ C) :
    IsWeaklyCompactOperator K :=
  weaklyCompact_of_bounded_range K (hk.apply_norm_le_of_bound hbound) hC

omit [SFinite μ] in
theorem hasKernelBound_of_uniform_bound (hk : Measurable k)
    (hbound : ∀ᵐ z ∂μ.prod ν, ‖k z‖ ≤ C) :
    HasKernelBound μ ν k (C * (ν univ).toReal) := by
  filter_upwards [Measure.ae_ae_of_ae_prod hbound] with x hx
  have hm : AEStronglyMeasurable (fun y => k (x, y)) ν :=
    (hk.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable
  have hi : Integrable (fun y => k (x, y)) ν :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hm C hx)
  refine ⟨hi, ?_⟩
  have h := integral_mono_ae hi.norm (integrable_const C) hx
  simpa only [integral_const, smul_eq_mul, measureReal_def, mul_comm] using h

theorem weaklyCompact_integralKernelOperator_of_uniform_bound (hk : Measurable k)
    (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂μ.prod ν, ‖k z‖ ≤ C) :
    IsWeaklyCompactOperator
      (integralKernelOperator hk (hasKernelBound_of_uniform_bound hk hbound)) :=
  (isIntegralKernel_integralKernelOperator hk
    (hasKernelBound_of_uniform_bound hk hbound)).weaklyCompact_of_bound hC hbound

end Kernels
end ThesisCommon
