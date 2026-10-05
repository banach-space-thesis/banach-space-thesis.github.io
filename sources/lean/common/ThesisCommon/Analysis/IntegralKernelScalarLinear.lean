import ThesisCommon.Analysis.IntegralKernel

/-! Scalar-uniform linear operations on actual integral kernels. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {k h : X × Y → 𝕜} {K H : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν}

theorem isIntegralKernel_zero_rclike : IsIntegralKernel (fun _ : X × Y => (0 : 𝕜))
    (0 : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν) where
  measurable := measurable_const
  integrable_section f := Eventually.of_forall fun _ => by simp
  represents f := by
    simpa only [zero_mul, integral_zero, ContinuousLinearMap.zero_apply] using Lp.coeFn_zero 𝕜 1 ν

theorem IsIntegralKernel.add_rclike (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    IsIntegralKernel (fun z => k z + h z) (K + H) where
  measurable := hk.measurable.add hh.measurable
  integrable_section f := by
    filter_upwards [hk.integrable_section f, hh.integrable_section f] with y hy hy'
    simpa only [add_mul] using hy.add hy'
  represents f := by
    filter_upwards [hk.represents f, hh.represents f, Lp.coeFn_add (K f) (H f),
      hk.integrable_section f, hh.integrable_section f] with y hy hy' hadd hi hi'
    change (K f + H f) y = _
    rw [hadd, Pi.add_apply, hy, hy', ← integral_add hi hi']
    simp only [add_mul]

theorem IsIntegralKernel.smul_rclike (hk : IsIntegralKernel k K) (a : 𝕜) :
    IsIntegralKernel (fun z => a * k z) (a • K) where
  measurable := measurable_const.mul hk.measurable
  integrable_section f := by
    filter_upwards [hk.integrable_section f] with y hy
    simpa only [mul_assoc] using hy.const_mul a
  represents f := by
    filter_upwards [hk.represents f, Lp.coeFn_smul a (K f)] with y hy hs
    change (a • K f) y = _
    rw [hs, Pi.smul_apply, smul_eq_mul, hy, ← integral_const_mul]
    simp only [mul_assoc]

theorem IsIntegralKernel.sub_rclike (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    IsIntegralKernel (fun z => k z - h z) (K - H) := by
  simpa only [neg_one_mul, neg_smul, one_smul, ← sub_eq_add_neg] using
    hk.add_rclike (hh.smul_rclike (-1))

end ThesisCommon
