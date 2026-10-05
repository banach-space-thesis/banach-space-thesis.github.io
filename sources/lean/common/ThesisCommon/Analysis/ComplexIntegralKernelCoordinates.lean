import ThesisCommon.Analysis.ComplexL1OperatorPhases
import ThesisCommon.Analysis.IntegralKernelScalarLinear
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Real and imaginary coordinates of genuine complex integral kernels,
and the complex kernel of the actual complexification of a real operator. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

section Complex
variable {k : X × Y → ℂ} {K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}

theorem IsIntegralKernel.integrable_real_input (hk : IsIntegralKernel k K)
    (f : Lp ℝ 1 μ) : ∀ᵐ y ∂ν, Integrable (fun x => k (x,y) * (f x : ℂ)) μ := by
  filter_upwards [hk.integrable_section (complexL1OfReal μ f)] with y hy
  apply hy.congr
  filter_upwards [complexL1OfReal_coe f] with x hx
  rw [hx]

theorem IsIntegralKernel.represents_real_input (hk : IsIntegralKernel k K)
    (f : Lp ℝ 1 μ) :
    K (complexL1OfReal μ f) =ᵐ[ν] fun y => ∫ x, k (x,y) * (f x : ℂ) ∂μ := by
  filter_upwards [hk.represents (complexL1OfReal μ f)] with y hy
  exact hy.trans (integral_congr_ae ((complexL1OfReal_coe f).mono fun x hx => congrArg (fun a : ℂ => k (x,y) * a) hx))

theorem IsIntegralKernel.real_coordinate (hk : IsIntegralKernel k K) :
    IsIntegralKernel (fun z => (k z).re)
      ((complexL1Re ν).comp (complexL1OperatorRealRestriction K)) where
  measurable := Complex.continuous_re.measurable.comp hk.measurable
  integrable_section f := by
    filter_upwards [hk.integrable_real_input f] with y hy
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using hy.re
  represents f := by
    filter_upwards [hk.represents_real_input f, hk.integrable_real_input f,
      complexL1Re_coe (K (complexL1OfReal μ f))] with y hy hi hre
    change complexL1Re ν (K (complexL1OfReal μ f)) y = _
    rw [hre, hy]
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using (integral_re hi).symm

theorem IsIntegralKernel.imag_coordinate (hk : IsIntegralKernel k K) :
    IsIntegralKernel (fun z => (k z).im)
      ((complexL1Im ν).comp (complexL1OperatorRealRestriction K)) where
  measurable := Complex.continuous_im.measurable.comp hk.measurable
  integrable_section f := by
    filter_upwards [hk.integrable_real_input f] with y hy
    simpa only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add] using hy.im
  represents f := by
    filter_upwards [hk.represents_real_input f, hk.integrable_real_input f,
      complexL1Im_coe (K (complexL1OfReal μ f))] with y hy hi him
    change complexL1Im ν (K (complexL1OfReal μ f)) y = _
    rw [him, hy]
    simpa only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add] using (integral_im hi).symm

end Complex

section Real
variable {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem realKernel_complex_input_decomposition (k : X × Y → ℝ)
    (f : Lp ℂ 1 μ) (y : Y) :
    (fun x => (k (x,y) : ℂ) * f x) =ᵐ[μ]
      (fun x => ((k (x,y) * complexL1Re μ f x : ℝ) : ℂ) +
        Complex.I * ((k (x,y) * complexL1Im μ f x : ℝ) : ℂ)) := by
  filter_upwards [complexL1Re_coe f, complexL1Im_coe f] with x hr hi
  rw [hr, hi]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem IsIntegralKernel.integrable_complex_input (hk : IsIntegralKernel k K)
    (f : Lp ℂ 1 μ) :
    ∀ᵐ y ∂ν, Integrable (fun x => (k (x,y) : ℂ) * f x) μ := by
  filter_upwards [hk.integrable_section (complexL1Re μ f),
    hk.integrable_section (complexL1Im μ f)] with y hr hi
  exact (hr.ofReal.add (hi.ofReal.const_mul Complex.I)).congr
    (realKernel_complex_input_decomposition k f y).symm

theorem IsIntegralKernel.complex_extension (hk : IsIntegralKernel k K) :
    IsIntegralKernel (fun z => (k z : ℂ)) (complexL1Extension K) where
  measurable := Complex.continuous_ofReal.measurable.comp hk.measurable
  integrable_section := hk.integrable_complex_input
  represents f := by
    filter_upwards [hk.represents (complexL1Re μ f), hk.represents (complexL1Im μ f),
      hk.integrable_section (complexL1Re μ f), hk.integrable_section (complexL1Im μ f),
      complexL1OfReal_coe (K (complexL1Re μ f)), complexL1OfReal_coe (K (complexL1Im μ f)),
      Lp.coeFn_smul Complex.I (complexL1OfReal ν (K (complexL1Im μ f))),
      Lp.coeFn_add (complexL1OfReal ν (K (complexL1Re μ f)))
        (Complex.I • complexL1OfReal ν (K (complexL1Im μ f)))]
      with y hkr hki hr hi hcr hci hs ha
    change (complexL1OfReal ν (K (complexL1Re μ f)) +
      Complex.I • complexL1OfReal ν (K (complexL1Im μ f))) y = _
    rw [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, hcr, hci, hkr, hki]
    symm
    calc
      (∫ x, (k (x,y) : ℂ) * f x ∂μ) =
          ∫ x, ((k (x,y) * complexL1Re μ f x : ℝ) : ℂ) +
            Complex.I * ((k (x,y) * complexL1Im μ f x : ℝ) : ℂ) ∂μ :=
        integral_congr_ae (realKernel_complex_input_decomposition k f y)
      _ = _ := by
        have hrC : Integrable (fun x => ((k (x,y) * complexL1Re μ f x : ℝ) : ℂ)) μ := hr.ofReal
        have hiC : Integrable (fun x => ((k (x,y) * complexL1Im μ f x : ℝ) : ℂ)) μ := hi.ofReal
        rw [integral_add hrC (hiC.const_mul Complex.I), integral_const_mul,
          integral_complex_ofReal, integral_complex_ofReal]

end Real

theorem isIntegralKernel_complex_coordinates_iff
    {k : X × Y → ℂ} {K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν} :
    IsIntegralKernel k K ↔
      IsIntegralKernel (fun z => (k z).re) (complexL1OperatorRe K) ∧
      IsIntegralKernel (fun z => (k z).im) (complexL1OperatorIm K) := by
  constructor
  · exact fun hk => ⟨hk.real_coordinate, hk.imag_coordinate⟩
  · rintro ⟨hr, hi⟩
    have h := hr.complex_extension.add_rclike (hi.complex_extension.smul_rclike Complex.I)
    have hfun : (fun z => ((k z).re : ℂ) + Complex.I * ((k z).im : ℂ)) = k := by
      funext z
      simpa only [mul_comm Complex.I] using Complex.re_add_im (k z)
    have hop : complexL1Extension (complexL1OperatorRe K) +
        Complex.I • complexL1Extension (complexL1OperatorIm K) = K :=
      (complexL1Operator_decomposition K).symm
    simpa only [hfun, hop] using h

theorem isIntegralOperator_complex_coordinates_iff
    (K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    IsIntegralOperator K ↔ IsIntegralOperator (complexL1OperatorRe K) ∧
      IsIntegralOperator (complexL1OperatorIm K) := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨⟨_, hk.real_coordinate⟩, ⟨_, hk.imag_coordinate⟩⟩
  · rintro ⟨⟨k, hk⟩, ⟨h, hh⟩⟩
    refine ⟨fun z => (k z : ℂ) + Complex.I * (h z : ℂ), ?_⟩
    have hs := hk.complex_extension.add_rclike (hh.complex_extension.smul_rclike Complex.I)
    have hop : complexL1Extension (complexL1OperatorRe K) +
        Complex.I • complexL1Extension (complexL1OperatorIm K) = K :=
      (complexL1Operator_decomposition K).symm
    rwa [hop] at hs

end ThesisCommon
