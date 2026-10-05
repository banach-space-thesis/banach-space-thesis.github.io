import ThesisCommon.Analysis.L1BoundedRangeDomination
import ThesisCommon.Analysis.IntegralPrincipalBand
import ThesisCommon.Analysis.L1AdjointOneRestriction

/-! Positive bounded-range approximants are integral on finite measure
spaces. The genuine integral band is norm closed, and each bounded-range
positive operator is dominated by a multiple of its rank-one generator.
The approximation property also survives positive contractive input maps,
in particular zero extension from arbitrary measurable input pieces. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y} {η : Measure Z}

theorem isClosed_integralOperatorSubmodule [SigmaFinite μ] [SigmaFinite ν] :
    IsClosed (integralOperatorSubmodule μ ν : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)) := by
  have he : (integralOperatorSubmodule μ ν : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)) =
      {T | integralBandProjection T = T} := by
    ext T
    constructor
    · exact integralBandProjection_eq_self
    · intro h
      exact h ▸ integralBandProjection_isIntegral T
  rw [he]
  exact isClosed_eq integralBandProjection.continuous continuous_id

theorem lOneOperator_le_rankOne_of_bounded_range [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} {C : ℝ}
    (hB : ∀ f, ∀ᵐ y ∂ν, ‖B f y‖ ≤ C * ‖f‖) :
    B ≤ C • integralRankOne μ ν := by
  intro f hf
  change B f ≤ C • (integralRankOne μ ν f)
  rw [integralRankOne_apply, smul_smul]
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [hB f, Lp.coeFn_smul (C * ∫ x, f x ∂μ)
    (lOneIndicator ν univ MeasurableSet.univ),
    lOneIndicator_coe (μ := ν) univ MeasurableSet.univ] with y hb hs hone
  change B f y ≤ ((C * ∫ x, f x ∂μ) • lOneIndicator ν univ MeasurableSet.univ) y
  rw [hs, Pi.smul_apply, smul_eq_mul, hone]
  simp only [indicator_univ, mul_one]
  exact (le_abs_self (B f y)).trans (by
    simpa only [Real.norm_eq_abs, lOne_norm_eq_integral_of_nonneg f hf] using hb)

theorem isIntegralOperator_of_positive_bounded_range [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hB : 0 ≤ B) {C : ℝ}
    (hbound : ∀ f, ∀ᵐ y ∂ν, ‖B f y‖ ≤ C * ‖f‖) : IsIntegralOperator B := by
  apply integralOperatorOrderClosedIdeal.nonneg_le_mem
    ((integralOperatorSubmodule μ ν).smul_mem C integralRankOne_isIntegral) hB
  exact lOneOperator_le_rankOne_of_bounded_range hbound

theorem HasPositiveBoundedRangeApproximants.isIntegral [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hH : HasPositiveBoundedRangeApproximants H) :
    IsIntegralOperator H := by
  change H ∈ (integralOperatorSubmodule μ ν : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν))
  rw [← (isClosed_integralOperatorSubmodule (μ := μ) (ν := ν)).closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨B, hB, _, herr, C, _, hbound⟩ := hH ε hε
  exact ⟨B, isIntegralOperator_of_positive_bounded_range hB hbound, by
    simpa only [dist_eq_norm] using herr⟩

theorem HasPositiveBoundedRangeApproximants.comp_positive_contraction
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hH : HasPositiveBoundedRangeApproximants H)
    (J : Lp ℝ 1 η →L[ℝ] Lp ℝ 1 μ) (hJ : 0 ≤ J) (hnJ : ‖J‖ ≤ 1) :
    HasPositiveBoundedRangeApproximants (H.comp J) := by
  intro ε hε
  obtain ⟨B, hB, hBH, herr, C, hC, hbound⟩ := hH ε hε
  refine ⟨B.comp J, (fun f hf => hB _ (hJ f hf)),
    (fun f hf => hBH _ (hJ f hf)), ?_, C, hC, ?_⟩
  · rw [← ContinuousLinearMap.sub_comp]
    exact ((ContinuousLinearMap.opNorm_comp_le (H - B) J).trans
      (mul_le_of_le_one_right (norm_nonneg _) hnJ)).trans_lt herr
  · intro f
    filter_upwards [hbound (J f)] with y hy
    exact hy.trans (mul_le_mul_of_nonneg_left
      ((J.le_opNorm f).trans (mul_le_of_le_one_left (norm_nonneg f) hnJ)) hC)

theorem HasPositiveBoundedRangeApproximants.comp_lebesgueLpExtend
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hH : HasPositiveBoundedRangeApproximants H)
    (s : Set X) (hs : MeasurableSet s) :
    HasPositiveBoundedRangeApproximants
      (H.comp (lebesgueLpExtend (𝕜 := ℝ) s hs).toContinuousLinearMap) :=
  hH.comp_positive_contraction _ (fun f hf => lebesgueL1Extend_nonneg s hs f hf)
    (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) s hs).norm_toContinuousLinearMap_le

theorem HasPositiveBoundedRangeApproximants.isIntegral_comp_lebesgueLpExtend
    [IsFiniteMeasure ν] {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hH : HasPositiveBoundedRangeApproximants H) (s : Set X) (hs : MeasurableSet s)
    [IsFiniteMeasure (μ.restrict s)] :
    IsIntegralOperator (H.comp (lebesgueLpExtend (𝕜 := ℝ) s hs).toContinuousLinearMap) :=
  (hH.comp_lebesgueLpExtend s hs).isIntegral

end ThesisCommon
