import ThesisCommon.Analysis.IntegralKernelPositive

/-! Dominated kernels and the paper's truncations. These estimates justify
constructing truncated and clipped bounded integral operators from kernels. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} {k h : X × Y → 𝕜} {C : ℝ}

theorem HasKernelBound.mono (hk : HasKernelBound μ ν k C) (hh : Measurable h)
    (hdom : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ‖h (x, y)‖ ≤ ‖k (x, y)‖) :
    HasKernelBound μ ν h C := by
  filter_upwards [hk, hdom] with x hx hdx
  have hm : AEStronglyMeasurable (fun y => h (x, y)) ν :=
    (hh.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable
  have hi := hx.1.mono hm hdx
  exact ⟨hi, (integral_mono_ae hi.norm hx.1.norm hdx).trans hx.2⟩

theorem HasKernelBound.truncatedKernel (hbound : HasKernelBound μ ν k C)
    (hk : Measurable k) (r : ℝ) : HasKernelBound μ ν (truncatedKernel r k) C := by
  apply hbound.mono (measurable_truncatedKernel hk r)
  exact Filter.Eventually.of_forall fun x =>
    Filter.Eventually.of_forall fun y => norm_truncatedKernel_le r k (x, y)

variable [SFinite μ] [SFinite ν]

/-- The actual truncated bounded operator K_r of Definition 3.13. -/
def truncatedKernelOperator (hk : Measurable k) (hbound : HasKernelBound μ ν k C) (r : ℝ) :
    Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν :=
  integralKernelOperator (measurable_truncatedKernel hk r) (hbound.truncatedKernel hk r)

theorem isIntegralKernel_truncatedKernelOperator (hk : Measurable k)
    (hbound : HasKernelBound μ ν k C) (r : ℝ) :
    IsIntegralKernel (truncatedKernel r k) (truncatedKernelOperator hk hbound r) :=
  isIntegralKernel_integralKernelOperator _ _

theorem norm_truncatedKernelOperator_le (hk : Measurable k)
    (hbound : HasKernelBound μ ν k C) (hC : 0 ≤ C) (r : ℝ) :
    ‖truncatedKernelOperator hk hbound r‖ ≤ C := norm_integralKernelOperator_le _ _ hC

section Positive
variable [IsFiniteMeasure μ] {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

/-- For positive kernels the column estimate is derived from the given
operator, so truncation requires no additional analytic assumption. -/
def positiveTruncatedKernelOperator (hk : IsIntegralKernel k K)
    (hpos : ∀ z, 0 ≤ k z) (r : ℝ) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  truncatedKernelOperator hk.measurable (hasKernelBound_of_nonneg hk hpos) r

theorem isIntegralKernel_positiveTruncatedKernelOperator (hk : IsIntegralKernel k K)
    (hpos : ∀ z, 0 ≤ k z) (r : ℝ) :
    IsIntegralKernel (truncatedKernel r k) (positiveTruncatedKernelOperator hk hpos r) :=
  isIntegralKernel_truncatedKernelOperator _ _ _

theorem norm_positiveTruncatedKernelOperator_le (hk : IsIntegralKernel k K)
    (hpos : ∀ z, 0 ≤ k z) (r : ℝ) : ‖positiveTruncatedKernelOperator hk hpos r‖ ≤ ‖K‖ :=
  norm_truncatedKernelOperator_le _ _ (norm_nonneg K) r

end Positive

end ThesisCommon
