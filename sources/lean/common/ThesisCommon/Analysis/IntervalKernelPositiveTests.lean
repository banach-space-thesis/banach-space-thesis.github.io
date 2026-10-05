import ThesisCommon.Analysis.IntervalKernelResidual
import ThesisCommon.Analysis.ContinuousMapPositiveSemicontinuity

/-! Measurability of moving nonnegative tests against the control measures.
Jordan parts need only lower semicontinuity on these tests. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem continuous_intervalKernel_transformed_test
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (φ : 𝕜 →L[ℝ] ℝ)
    (f : UnitInterval → C(UnitInterval, ℝ)) (hf : Continuous f) :
    Continuous (fun t => φ (intervalOperatorKernel T t (continuousMapOfReal (f t)))) := by
  exact φ.continuous.comp (continuous_eval.comp
    ((T.continuous.comp (continuousMapOfReal.continuous.comp hf)).prodMk continuous_id))

theorem measurable_intervalKernel_positive_tests
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (f : UnitInterval → C(UnitInterval, ℝ)) (hf : Continuous f) (hpos : ∀ t, 0 ≤ f t) :
    Measurable (fun t =>
      continuousMapPositivePart (continuousMapFunctionalRe (intervalOperatorKernel T t)) (f t)) ∧
    Measurable (fun t =>
      continuousMapNegativePart (continuousMapFunctionalRe (intervalOperatorKernel T t)) (f t)) ∧
    Measurable (fun t =>
      continuousMapPositivePart (continuousMapFunctionalIm (intervalOperatorKernel T t)) (f t)) ∧
    Measurable (fun t =>
      continuousMapNegativePart (continuousMapFunctionalIm (intervalOperatorKernel T t)) (f t)) := by
  have hr (g : C(UnitInterval, ℝ)) : Continuous (fun t =>
      continuousMapFunctionalRe (intervalOperatorKernel T t) (g⁺ ⊓ f t)) :=
    continuous_intervalKernel_transformed_test T RCLike.reCLM _
      (continuous_continuousMap_clip f hf g)
  have hi (g : C(UnitInterval, ℝ)) : Continuous (fun t =>
      continuousMapFunctionalIm (intervalOperatorKernel T t) (g⁺ ⊓ f t)) :=
    continuous_intervalKernel_transformed_test T RCLike.imCLM _
      (continuous_continuousMap_clip f hf g)
  refine ⟨(lowerSemicontinuous_continuousMapPositivePart_test _ f hpos hr).measurable, ?_,
    (lowerSemicontinuous_continuousMapPositivePart_test _ f hpos hi).measurable, ?_⟩
  · simp_rw [continuousMapNegativePart_eq_positive_neg]
    exact (lowerSemicontinuous_continuousMapPositivePart_test _ f hpos
      (fun g => (hr g).neg)).measurable
  · simp_rw [continuousMapNegativePart_eq_positive_neg]
    exact (lowerSemicontinuous_continuousMapPositivePart_test _ f hpos
      (fun g => (hi g).neg)).measurable

theorem integral_continuousMapRieszControl_real (μ : C(UnitInterval, 𝕜) →L[𝕜] 𝕜)
    (f : C(UnitInterval, ℝ)) :
    ∫ x, f x ∂continuousMapRieszControl μ =
      (continuousMapPositivePart (continuousMapFunctionalRe μ) f +
        continuousMapNegativePart (continuousMapFunctionalRe μ) f) +
      (continuousMapPositivePart (continuousMapFunctionalIm μ) f +
        continuousMapNegativePart (continuousMapFunctionalIm μ) f) := by
  have hf (ν : Measure UnitInterval) [IsFiniteMeasure ν] : Integrable f ν :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  unfold continuousMapRieszControl
  rw [integral_add_measure (hf _) (hf _), integral_add_measure (hf _) (hf _),
    integral_add_measure (hf _) (hf _)]
  simp only [continuousMapRieszPositive, continuousMapRieszNegative,
    integral_continuousMapRieszMeasure]
  rfl

theorem measurable_intervalKernel_control_integral
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (f : UnitInterval → C(UnitInterval, ℝ)) (hf : Continuous f) (hpos : ∀ t, 0 ≤ f t) :
    Measurable (fun t => ∫ x, f t x ∂continuousMapRieszControl (intervalOperatorKernel T t)) := by
  simp_rw [integral_continuousMapRieszControl_real]
  obtain ⟨hrp, hrn, hip, hin⟩ := measurable_intervalKernel_positive_tests T f hf hpos
  exact (hrp.add hrn).add (hip.add hin)

end ThesisCommon
