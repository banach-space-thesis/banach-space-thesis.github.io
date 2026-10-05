import ThesisCommon.Analysis.KernelSingularTailBound
import ThesisCommon.Analysis.KernelProductRestriction

/-! The reverse kernel consisting of the singular part and the large-value
tail of the absolutely continuous part. All fibre masses and its product
measure are calculated for the actual measurable finite kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [MeasurableSpace.CountableOrCountablyGenerated X Y]
variable (κ : Kernel X Y) [IsFiniteKernel κ] (ν : Measure Y) [IsFiniteMeasure ν]

def kernelTailRemainder (r : ℝ) : Kernel X Y :=
  kernelSingularPart κ ν + productSetKernel (kernelAbsolutelyContinuousPart κ ν)
    {z | r ≤ kernelRealDensity κ ν z}

instance kernelTailRemainder_finite (r : ℝ) : IsFiniteKernel (kernelTailRemainder κ ν r) := by
  unfold kernelTailRemainder
  infer_instance

theorem kernelTailRemainder_real_univ (r : ℝ) (x : X) :
    (kernelTailRemainder κ ν r x).real univ = (kernelSingularPart κ ν x).real univ +
      ∫ y in {y | r ≤ kernelRealDensity κ ν (x, y)}, kernelRealDensity κ ν (x, y) ∂ν := by
  rw [kernelTailRemainder, Kernel.add_apply, measureReal_add_apply,
    productSetKernel_apply _ _ (measurableSet_le measurable_const (measurable_kernelRealDensity κ ν))]
  congr 1
  rw [measureReal_def, Measure.restrict_apply_univ, kernelAbsolutelyContinuousPart_apply]
  have hm : MeasurableSet (Prod.mk x ⁻¹' {z | r ≤ kernelRealDensity κ ν z}) :=
    measurable_prodMk_left (measurableSet_le measurable_const (measurable_kernelRealDensity κ ν))
  rw [withDensity_apply _ hm,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_kernelRealDensity_column κ ν x).integrableOn
      (Eventually.of_forall fun y => kernelRealDensity_nonneg κ ν (x, y)),
    ENNReal.toReal_ofReal (integral_nonneg fun y => kernelRealDensity_nonneg κ ν (x, y))]
  rfl

theorem compProd_kernelTailRemainder (μ : Measure X) [SFinite μ] (r : ℝ) :
    μ ⊗ₘ kernelTailRemainder κ ν r = μ ⊗ₘ kernelSingularPart κ ν +
      (μ.prod ν).withDensity (fun z => ENNReal.ofReal (truncatedKernel r (kernelRealDensity κ ν) z)) := by
  rw [kernelTailRemainder, Measure.compProd_add_right, compProd_productSetKernel _ _ _
    (measurableSet_le measurable_const (measurable_kernelRealDensity κ ν)),
    compProd_kernelAbsolutelyContinuousPart, restrict_withDensity
      (measurableSet_le measurable_const (measurable_kernelRealDensity κ ν)),
      ← withDensity_indicator (measurableSet_le measurable_const (measurable_kernelRealDensity κ ν))]
  congr 2
  funext z
  by_cases hz : r ≤ kernelRealDensity κ ν z
  · simp [truncatedKernel, Real.norm_eq_abs, abs_of_nonneg (kernelRealDensity_nonneg κ ν z), hz]
  · simp [truncatedKernel, Real.norm_eq_abs, abs_of_nonneg (kernelRealDensity_nonneg κ ν z), hz]

theorem ae_kernelTailRemainder_mass_bound [MeasurableSpace.CountablyGenerated Y]
    {μ : Measure X} {δ C M r : ℝ} (hr : 0 < r) (hMr : M / r < δ)
    (hmass : ∀ᵐ x ∂μ, (κ x).real univ ≤ M)
    (htest : ∀ B : Set Y, MeasurableSet B → ν.real B < δ →
      ∀ᵐ x ∂μ, (κ x).real B ≤ C) :
    ∀ᵐ x ∂μ, (kernelTailRemainder κ ν r x).real univ ≤ C := by
  simpa only [kernelTailRemainder_real_univ] using
    ae_kernel_singular_tail_bound κ hr hMr hmass htest

end ThesisCommon
