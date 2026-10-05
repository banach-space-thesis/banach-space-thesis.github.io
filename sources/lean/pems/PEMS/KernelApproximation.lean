import ThesisCommon.Analysis.IntegralKernelApproximation

/-! Constructed weakly compact approximants used in the upper-bound
direction of the standard-space formula. The best approximant and matching
lower bound in Theorem 4.1 are distinct remaining obligations. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [IsFiniteMeasure ν]
variable {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem exists_weakly_compact_truncation_approximant (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (r : ℝ) :
    ∃ W : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, IsWeaklyCompactOperator W ∧
      S + K - W = S + truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite r :=
  ⟨boundedKernelApproximation hk r, weaklyCompact_boundedKernelApproximation hk r,
    sub_boundedKernelApproximation hk r S⟩

theorem weis_truncation_upper_bound (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    weakEssentialNorm (S + K) ≤ sInf (Set.range (fun n : ℕ =>
      ‖S + truncatedKernelOperator hk.measurable hk.hasKernelBound_sigmaFinite n‖)) :=
  weakEssentialNorm_le_truncation_inf hk S

end PEMS
