import ThesisCommon.Analysis.IntegralKernelTests

/-! Order and uniqueness of real integral kernels. On a finite input space,
order of the actual operators is equivalent to almost-everywhere order of
their kernels. These are the kernel-order preliminaries for integral bands. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {k h : X × Y → ℝ} {K H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem IsIntegralKernel.sub (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    IsIntegralKernel (fun z => k z - h z) (K - H) where
  measurable := hk.measurable.sub hh.measurable
  integrable_section f := by
    filter_upwards [hk.integrable_section f, hh.integrable_section f] with y hki hhi
    simpa only [sub_mul] using hki.sub hhi
  represents f := by
    filter_upwards [hk.represents f, hh.represents f, Lp.coeFn_sub (K f) (H f),
      hk.integrable_section f, hh.integrable_section f] with y hky hhy hsub hki hhi
    change (K f - H f) y = _
    rw [hsub, Pi.sub_apply, hky, hhy, ← integral_sub hki hhi]
    simp only [sub_mul]

theorem IsIntegralKernel.positive_of_nonneg_ae [SFinite μ] [SFinite ν]
    (hk : IsIntegralKernel k K) (hpos : ∀ᵐ z ∂μ.prod ν, 0 ≤ k z) :
    ∀ f : Lp ℝ 1 μ, 0 ≤ f → 0 ≤ K f := by
  intro f hf
  have hm : MeasurableSet {z : X × Y | 0 ≤ k z} :=
    measurableSet_le measurable_const hk.measurable
  have hsections := (Measure.ae_ae_comm hm).mp ((Measure.ae_prod_iff_ae_ae hm).mp hpos)
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [hk.represents f, hsections] with y hy hky
  rw [hy]
  apply integral_nonneg_of_ae
  filter_upwards [hky, (Lp.coeFn_nonneg f).mpr hf] with x hx hfx
  exact mul_nonneg hx hfx

theorem IsIntegralKernel.positive_iff_nonneg_ae [IsFiniteMeasure μ] [SFinite ν]
    (hk : IsIntegralKernel k K) :
    (∀ f : Lp ℝ 1 μ, 0 ≤ f → 0 ≤ K f) ↔ ∀ᵐ z ∂μ.prod ν, 0 ≤ k z :=
  ⟨hk.nonneg_ae_of_positive, hk.positive_of_nonneg_ae⟩

theorem IsIntegralKernel.le_iff_kernel_le [IsFiniteMeasure μ] [SFinite ν]
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    (∀ f : Lp ℝ 1 μ, 0 ≤ f → K f ≤ H f) ↔ k ≤ᵐ[μ.prod ν] h := by
  have heq := (hh.sub hk).positive_iff_nonneg_ae
  simpa only [ContinuousLinearMap.sub_apply, sub_nonneg] using heq

/-- Uniqueness here concerns the kernel up to product-null sets. This is
different from `IsIntegralKernel.unique`, which fixes a kernel and identifies
the represented bounded operators. -/
theorem IsIntegralKernel.kernel_unique [IsFiniteMeasure μ] [SFinite ν]
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h K) : k =ᵐ[μ.prod ν] h := by
  have hkh := (hk.le_iff_kernel_le hh).mp (fun _ _ => le_rfl)
  have hhk := (hh.le_iff_kernel_le hk).mp (fun _ _ => le_rfl)
  filter_upwards [hkh, hhk] with z hz hz'
  exact le_antisymm hz hz'

theorem IsIntegralKernel.congr_ae [SFinite μ] [SFinite ν]
    (hk : IsIntegralKernel k K) (hh : Measurable h) (heq : k =ᵐ[μ.prod ν] h) :
    IsIntegralKernel h K := by
  have hm : MeasurableSet {z | k z = h z} := measurableSet_eq_fun hk.measurable hh
  have hsections := (Measure.ae_ae_comm hm).mp ((Measure.ae_prod_iff_ae_ae hm).mp heq)
  refine ⟨hh, ?_, ?_⟩
  · intro f
    filter_upwards [hk.integrable_section f, hsections] with y hy heqy
    exact hy.congr (heqy.mono fun x hx => congrArg (fun a => a * f x) hx)
  · intro f
    filter_upwards [hk.represents f, hsections] with y hy heqy
    exact hy.trans (integral_congr_ae (heqy.mono fun x hx => congrArg (fun a => a * f x) hx))

end ThesisCommon
