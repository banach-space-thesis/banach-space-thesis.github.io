import ThesisCommon.Analysis.IntegralKernelWeakCompact
import ThesisCommon.Analysis.IntegralKernelSigmaFiniteBound
import ThesisCommon.Analysis.IntegralKernelDomination
import ThesisCommon.Analysis.IntegralSingularModulus

/-! The bounded complements of the paper's large-value truncated kernels
give actual weakly compact approximants. These are the upper estimates in
the Weis formula, before its converse and best-approximation assertions. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem norm_sub_truncatedKernel_le (r : ℝ) (k : X × Y → ℝ) (z : X × Y) :
    ‖k z - truncatedKernel r k z‖ ≤ max r 0 := by
  by_cases h : r ≤ ‖k z‖
  · rw [truncatedKernel, Set.indicator_of_mem (show z ∈ {w | r ≤ ‖k w‖} from h),
      sub_self, norm_zero]
    exact le_max_right r 0
  · rw [truncatedKernel, Set.indicator_of_notMem (show z ∉ {w | r ≤ ‖k w‖} from h), sub_zero]
    exact (le_of_lt (lt_of_not_ge h)).trans (le_max_left r 0)

theorem IsIntegralKernel.hasKernelBound_iff_norm_le [SigmaFinite μ] [SFinite ν]
    (hk : IsIntegralKernel k K) {C : ℝ} (hC : 0 ≤ C) :
    HasKernelBound μ ν k C ↔ ‖K‖ ≤ C := by
  constructor
  · intro hb
    have heq := hk.unique (isIntegralKernel_integralKernelOperator hk.measurable hb)
    rw [heq]
    exact norm_integralKernelOperator_le _ _ hC
  · exact fun h => hk.hasKernelBound_sigmaFinite.mono_const h

variable [SigmaFinite μ] [IsFiniteMeasure ν]

/-- The paper's K_r retains the large values |k|>=r. Its complement is
bounded by max(r,0), including nonpositive thresholds and zero measures. -/
def boundedKernelApproximation (hk : IsIntegralKernel k K) (r : ℝ) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  K - truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r

theorem isIntegralKernel_boundedKernelApproximation (hk : IsIntegralKernel k K) (r : ℝ) :
    IsIntegralKernel (fun z => k z - truncatedKernel r k z) (boundedKernelApproximation hk r) :=
  hk.sub (isIntegralKernel_truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r)

theorem weaklyCompact_boundedKernelApproximation (hk : IsIntegralKernel k K) (r : ℝ) :
    IsWeaklyCompactOperator (boundedKernelApproximation hk r) :=
  (isIntegralKernel_boundedKernelApproximation hk r).weaklyCompact_of_bound (le_max_right r 0)
    (Eventually.of_forall (norm_sub_truncatedKernel_le r k))

theorem sub_boundedKernelApproximation (hk : IsIntegralKernel k K) (r : ℝ)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    S + K - boundedKernelApproximation hk r =
      S + truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r := by
  simp only [boundedKernelApproximation]
  abel

theorem weakEssentialNorm_le_truncated_remainder (hk : IsIntegralKernel k K) (r : ℝ)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    weakEssentialNorm (S + K) ≤
      ‖S + truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r‖ := by
  simpa only [sub_boundedKernelApproximation] using
    weakEssentialNorm_le (S + K) (weaklyCompact_boundedKernelApproximation hk r)

theorem weakEssentialNorm_le_truncation_inf (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    weakEssentialNorm (S + K) ≤
      sInf (Set.range (fun n : ℕ =>
        ‖S + truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite n‖)) := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact weakEssentialNorm_le_truncated_remainder hk n S

theorem singular_truncated_remainder_norm (hk : IsIntegralKernel k K)
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsSingularOperator S) (r : ℝ) :
    ‖S + truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r‖ =
      ‖|S| + |truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r|‖ := by
  rw [← norm_abs_lOneOperator, singular_integral_abs_add hS
    ⟨_, isIntegralKernel_truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r⟩]

end ThesisCommon
