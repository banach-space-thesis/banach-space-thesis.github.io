import ThesisCommon.Analysis.IntegralKernel
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! The positive-kernel argument in PEMS Proposition 3.14. For a general
signed/complex kernel, one must still establish the modulus-operator kernel
theorem before applying this result to |k|. No modulus theorem is assumed. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

/-- A nonnegative kernel representing a bounded L¹ operator is integrable on
the product when the input measure is finite. This is the paper's test-at-one
and Tonelli argument, prior to the signed/complex modulus reduction. -/
theorem integrable_kernel_of_nonneg {k : X × Y → ℝ}
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K)
    (hpos : ∀ z, 0 ≤ k z) : Integrable k (μ.prod ν) := by
  let oneL1 : Lp ℝ 1 μ := (integrable_const (1 : ℝ)).toL1 (fun _ : X => 1)
  have hone : oneL1 =ᵐ[μ] fun _ : X => (1 : ℝ) := Integrable.coeFn_toL1 _
  have hweighted (y : Y) : (fun x => k (x, y) * oneL1 x) =ᵐ[μ] fun x => k (x, y) := by
    filter_upwards [hone] with x hx
    simp [hx]
  have hsections : ∀ᵐ y ∂ν, Integrable (fun x => k (x, y)) μ := by
    filter_upwards [hk.integrable_section oneL1] with y hy
    exact hy.congr (hweighted y)
  have hrepr : K oneL1 =ᵐ[ν] fun y => ∫ x, ‖k (x, y)‖ ∂μ := by
    filter_upwards [hk.represents oneL1] with y hy
    rw [hy, integral_congr_ae (hweighted y)]
    congr 1
    funext x
    exact (Real.norm_of_nonneg (hpos (x, y))).symm
  exact (integrable_prod_iff' hk.measurable.stronglyMeasurable.aestronglyMeasurable).mpr
    ⟨hsections, (L1.integrable_coeFn (K oneL1)).congr hrepr⟩

/-- A positive kernel of an existing bounded operator has the sharp a.e.
column estimate. Testing characteristic functions gives the set-integral
inequality; the a.e. inequality is then deduced, not postulated. -/
theorem hasKernelBound_of_nonneg {k : X × Y → ℝ}
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K)
    (hpos : ∀ z, 0 ≤ k z) : HasKernelBound μ ν k ‖K‖ := by
  have hki := integrable_kernel_of_nonneg hk hpos
  have hcol : Integrable (fun x => ∫ y, k (x, y) ∂ν) μ := hki.integral_prod_left
  have hle : (fun x => ∫ y, k (x, y) ∂ν) ≤ᵐ[μ] fun _ => ‖K‖ := by
    apply ae_le_of_forall_setIntegral_le hcol (integrable_const _)
    intro s hs _
    let f : Lp ℝ 1 μ := ((integrable_const (1 : ℝ)).indicator hs).toL1 (s.indicator (fun _ => 1))
    have hf : f =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) := Integrable.coeFn_toL1 _
    have hweight (y : Y) : (fun x => k (x, y) * f x) =ᵐ[μ] s.indicator (fun x => k (x, y)) := by
      filter_upwards [hf] with x hx
      by_cases hxs : x ∈ s <;> simp [hx, hxs]
    have hKf : K f =ᵐ[ν] fun y => ∫ x in s, k (x, y) ∂μ := by
      filter_upwards [hk.represents f] with y hy
      rw [hy, integral_congr_ae (hweight y), integral_indicator hs]
    have hnorm : ‖K f‖ = ∫ y, ∫ x in s, k (x, y) ∂μ ∂ν := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [hKf] with y hy
      rw [hy, Real.norm_of_nonneg (integral_nonneg fun x => hpos (x, y))]
    have hfnorm : ‖f‖ = μ.real s := by
      rw [L1.norm_eq_integral_norm]
      calc
        (∫ x, ‖f x‖ ∂μ) = ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
          apply integral_congr_ae
          filter_upwards [hf] with x hx
          by_cases hxs : x ∈ s <;> simp [hx, hxs]
        _ = μ.real s := integral_indicator_one hs
    have hswap : (∫ x in s, ∫ y, k (x, y) ∂ν ∂μ) =
        ∫ y, ∫ x in s, k (x, y) ∂μ ∂ν := by
      have hprod : Integrable (fun z : X × Y => s.indicator (fun x => k (x, z.2)) z.1) (μ.prod ν) := by
        simpa only [indicator_comp_right] using hki.indicator (hs.preimage measurable_fst)
      have h := integral_integral_swap (μ := μ) (ν := ν)
        (f := fun x y => s.indicator (fun t => k (t, y)) x) hprod
      simpa only [← integral_indicator hs, integral_indicator₂] using h
    calc
      (∫ x in s, ∫ y, k (x, y) ∂ν ∂μ) = ‖K f‖ := hswap.trans hnorm.symm
      _ ≤ ‖K‖ * ‖f‖ := K.le_opNorm f
      _ = ∫ _ in s, ‖K‖ ∂μ := by rw [hfnorm, setIntegral_const, smul_eq_mul, mul_comm]
  filter_upwards [hki.prod_right_ae, hle] with x hix hx
  refine ⟨hix, ?_⟩
  simpa only [Real.norm_of_nonneg (hpos _)] using hx

end ThesisCommon
