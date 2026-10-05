import ThesisCommon.Analysis.IntegralKernelSigmaFiniteBound
import ThesisCommon.Analysis.IntegralSingularModulus

/-! Large-value truncation commutes with the actual real operator modulus.
Consequently the norm of a signed singular-plus-tail remainder equals the
norm of the positive singular modulus plus the tail of the absolute kernel. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem truncatedKernel_abs (k : X × Y → ℝ) (r : ℝ) :
    truncatedKernel r (fun z => |k z|) = fun z => |truncatedKernel r k z| := by
  funext z
  by_cases hz : r ≤ |k z| <;> simp [truncatedKernel, Real.norm_eq_abs, hz]

theorem IsIntegralKernel.abs [SFinite μ]
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) : IsIntegralKernel (fun z => |k z|) |K| := by
  simpa only [abs_lOneOperator_eq] using hk.modulus

theorem isIntegralKernel_abs_truncatedKernelOperator [SFinite μ] [SFinite ν]
    {k : X × Y → ℝ} {C : ℝ} (hk : Measurable k) (hb : HasKernelBound μ ν k C) (r : ℝ) :
    IsIntegralKernel (truncatedKernel r (fun z => |k z|)) |truncatedKernelOperator hk hb r| := by
  rw [truncatedKernel_abs]
  exact (isIntegralKernel_truncatedKernelOperator hk hb r).abs

theorem abs_truncatedKernelOperator [SFinite μ] [SFinite ν]
    {k : X × Y → ℝ} {C D : ℝ} (hk : Measurable k) (hb : HasKernelBound μ ν k C)
    (ha : Measurable (fun z => |k z|)) (hab : HasKernelBound μ ν (fun z => |k z|) D) (r : ℝ) :
    |truncatedKernelOperator hk hb r| = truncatedKernelOperator ha hab r :=
  (isIntegralKernel_abs_truncatedKernelOperator hk hb r).unique
    (isIntegralKernel_truncatedKernelOperator ha hab r)

theorem IsIntegralKernel.abs_truncatedOperator [IsFiniteMeasure μ] [SFinite ν]
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) (r : ℝ) :
    |hk.truncatedOperator r| = hk.abs.truncatedOperator r :=
  abs_truncatedKernelOperator hk.measurable hk.hasKernelBound
    hk.abs.measurable hk.abs.hasKernelBound r

theorem IsIntegralKernel.abs_truncatedKernelOperator_sigmaFinite [SigmaFinite μ] [SFinite ν]
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) (r : ℝ) :
    |truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r| =
      truncatedKernelOperator hk.abs.measurable hk.abs.hasKernelBound_sigmaFinite r :=
  abs_truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite
    hk.abs.measurable hk.abs.hasKernelBound_sigmaFinite r

theorem singular_truncated_remainder_norm_absKernel [SigmaFinite μ] [SFinite ν]
    {k : X × Y → ℝ} {K S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) (hS : IsSingularOperator S) (r : ℝ) :
    ‖S + truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r‖ =
      ‖|S| + truncatedKernelOperator hk.abs.measurable hk.abs.hasKernelBound_sigmaFinite r‖ := by
  rw [← norm_abs_lOneOperator, singular_integral_abs_add hS
    ⟨_, isIntegralKernel_truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r⟩,
    hk.abs_truncatedKernelOperator_sigmaFinite]

end ThesisCommon
