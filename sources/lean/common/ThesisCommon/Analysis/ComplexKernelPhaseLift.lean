import ThesisCommon.Analysis.ComplexIntegralKernelModulus
import ThesisCommon.Analysis.ComplexIntegralOperatorBand

/-! A positive integral fragment of a complex integral operator's modulus
has an actual phase lift. The kernel is scaled radially, including zero
columns, and both required modulus identities are proved exactly. -/
noncomputable section
open MeasureTheory Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def complexPhaseScale (z : ℂ) (r : ℝ) : ℂ := (r/‖z‖) • z

theorem norm_complexPhaseScale (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hrz : r ≤ ‖z‖) :
    ‖complexPhaseScale z r‖ = r := by
  by_cases hz : z = 0
  · have hr0 : r = 0 := le_antisymm (by simpa [hz] using hrz) hr
    simp [complexPhaseScale,hz,hr0]
  · rw [complexPhaseScale,norm_smul,Real.norm_of_nonneg (div_nonneg hr (norm_nonneg z)),
      div_mul_cancel₀ r (norm_ne_zero_iff.mpr hz)]

theorem norm_sub_complexPhaseScale (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hrz : r ≤ ‖z‖) :
    ‖z-complexPhaseScale z r‖ = ‖z‖-r := by
  by_cases hz : z = 0
  · have hr0 : r = 0 := le_antisymm (by simpa [hz] using hrz) hr
    simp [complexPhaseScale,hz,hr0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hc : 0 ≤ 1-r/‖z‖ := sub_nonneg.mpr ((div_le_one hn).mpr hrz)
    have he : z-complexPhaseScale z r = (1-r/‖z‖) • z := by
      rw [sub_smul,one_smul,complexPhaseScale]
    rw [he,norm_smul,Real.norm_of_nonneg hc,sub_mul,one_mul,div_mul_cancel₀ r hn.ne']

theorem measurable_complexPhaseScale {k : X × Y → ℂ} {h : X × Y → ℝ}
    (hk : Measurable k) (hh : Measurable h) : Measurable (fun z => complexPhaseScale (k z) (h z)) :=
  (hh.div hk.norm).smul hk

variable [SigmaFinite μ] [SigmaFinite ν]

theorem IsIntegralKernel.exists_complex_phaseLift
    {k : X × Y → ℂ} {K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν} (hk : IsIntegralKernel k K)
    {h : X × Y → ℝ} {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hh : IsIntegralKernel h H)
    (hH : 0 ≤ H) (hHK : H ≤ complexL1OperatorModulus K) :
    ∃ V : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν, IsIntegralOperator V ∧
      complexL1OperatorModulus V = H ∧
      complexL1OperatorModulus (K-V) = complexL1OperatorModulus K-H := by
  have hp : ∀ᵐ z ∂μ.prod ν, 0 ≤ h z := hh.nonneg_ae_of_positive_sigmaFinite hH
  have hle : ∀ᵐ z ∂μ.prod ν, h z ≤ ‖k z‖ :=
    (hh.le_iff_kernel_le_sigmaFinite hk.complex_modulus).mp hHK
  let v : X × Y → ℂ := fun z => complexPhaseScale (k z) (h z)
  have hv : Measurable v := measurable_complexPhaseScale hk.measurable hh.measurable
  have hnorm : ∀ᵐ z ∂μ.prod ν, ‖v z‖ = h z := by
    filter_upwards [hp,hle] with z hpz hlez
    exact norm_complexPhaseScale (k z) hpz hlez
  have hnormabs : ∀ᵐ z ∂μ.prod ν, ‖v z‖ = ‖h z‖ := by
    filter_upwards [hnorm,hp] with z hz hpz
    rw [hz,Real.norm_of_nonneg hpz]
  have hb : HasKernelBound μ ν v ‖H‖ := by
    filter_upwards [hh.hasKernelBound_sigmaFinite,Measure.ae_ae_of_ae_prod hnormabs] with x hx he
    have hm : AEStronglyMeasurable (fun y => v (x,y)) ν :=
      (hv.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    refine ⟨(integrable_norm_iff hm).mp (hx.1.norm.congr (Filter.EventuallyEq.symm he)),?_⟩
    rw [integral_congr_ae he]
    exact hx.2
  let V := integralKernelOperator hv hb
  have hvK : IsIntegralKernel v V := isIntegralKernel_integralKernelOperator hv hb
  have hMV : complexL1OperatorModulus V = H :=
    hvK.complex_modulus.unique (hh.congr_ae hv.norm (Filter.EventuallyEq.symm hnorm))
  refine ⟨V,⟨v,hvK⟩,hMV,?_⟩
  have herr : ∀ᵐ z ∂μ.prod ν, ‖k z-v z‖ = ‖k z‖-h z := by
    filter_upwards [hp,hle] with z hpz hlez
    exact norm_sub_complexPhaseScale (k z) hpz hlez
  exact (hk.sub_rclike hvK).complex_modulus.unique
    ((hk.complex_modulus.sub hh).congr_ae (hk.measurable.sub hv).norm (Filter.EventuallyEq.symm herr))

end ThesisCommon
