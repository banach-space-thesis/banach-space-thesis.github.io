import ThesisCommon.Analysis.SignedReverseKernel

/-! Rectangle integration for actual signed reverse kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integrable_kernel_real_eval (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X Y) [IsFiniteKernel κ] (b : Set Y) (hb : MeasurableSet b) :
    Integrable (fun x => (κ x).real b) μ := by
  apply integrable_toReal_of_lintegral_ne_top (Kernel.measurable_coe κ hb).aemeasurable
  rw [← setLIntegral_univ, ← Measure.compProd_apply_prod MeasurableSet.univ hb]
  exact measure_ne_top (μ ⊗ₘ κ) _

theorem setIntegral_kernel_real_eval (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X Y) [IsFiniteKernel κ] (a : Set X) (ha : MeasurableSet a)
    (b : Set Y) (hb : MeasurableSet b) :
    (∫ x in a, (κ x).real b ∂μ) = (μ ⊗ₘ κ).real (a ×ˢ b) := by
  rw [Measure.real, Measure.compProd_apply_prod ha hb]
  exact integral_toReal (Kernel.measurable_coe κ hb).aemeasurable.restrict
    (Filter.Eventually.of_forall fun x => measure_lt_top (κ x) b)

theorem SignedReverseKernel.fibre_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (K : SignedReverseKernel X Y) (b : Set Y) (hb : MeasurableSet b) :
    Integrable (fun x => K.fibre x b) μ := by
  have h : (fun x => K.fibre x b) =
      fun x => (K.posPart x).real b - (K.negPart x).real b := by
    funext x
    exact Measure.toSignedMeasure_sub_apply hb
  rw [h]
  exact (integrable_kernel_real_eval μ K.posPart b hb).sub
    (integrable_kernel_real_eval μ K.negPart b hb)

theorem SignedReverseKernel.fibre_setIntegral (μ : Measure X) [IsFiniteMeasure μ]
    (K : SignedReverseKernel X Y) (a : Set X) (ha : MeasurableSet a)
    (b : Set Y) (hb : MeasurableSet b) :
    (∫ x in a, K.fibre x b ∂μ) =
      (μ ⊗ₘ K.posPart).real (a ×ˢ b) - (μ ⊗ₘ K.negPart).real (a ×ˢ b) := by
  have h : (fun x => K.fibre x b) =
      fun x => (K.posPart x).real b - (K.negPart x).real b := by
    funext x
    exact Measure.toSignedMeasure_sub_apply hb
  rw [h, integral_sub (integrable_kernel_real_eval μ K.posPart b hb).integrableOn
    (integrable_kernel_real_eval μ K.negPart b hb).integrableOn,
    setIntegral_kernel_real_eval μ K.posPart a ha b hb,
    setIntegral_kernel_real_eval μ K.negPart a ha b hb]

variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

theorem signedOperator_reverseKernel_rectangle
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (K : SignedReverseKernel X Y)
    (hP : μ ⊗ₘ K.posPart = clopenOperatorMeasure T⁺ (posPart_nonneg T))
    (hN : μ ⊗ₘ K.negPart = clopenOperatorMeasure T⁻ (negPart_nonneg T))
    (a : Set X) (ha : MeasurableSet a) (b : Set Y) (hb : MeasurableSet b) :
    (∫ x in a, K.fibre x b ∂μ) = ∫ y in b, T (lOneIndicator μ a ha) y ∂ν := by
  rw [K.fibre_setIntegral μ a ha b hb, hP, hN,
    ← Measure.toSignedMeasure_sub_apply (ha.prod hb)]
  exact signedOperatorMeasure_rectangle T a ha b hb

end ThesisCommon
