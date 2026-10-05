import ThesisCommon.Analysis.PositiveOperatorDisintegration
import ThesisCommon.Analysis.KernelLebesgueDecomposition
import ThesisCommon.Analysis.ClopenOperatorLebesgue

/-! The jointly measurable fibre density of the reverse kernel represents
the actual integral part of a positive operator. Its measurable singular
kernel represents the product measure of the actual residual. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem isIntegralKernel_kernelRealDensity_of_operator
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hprod : μ ⊗ₘ κ = clopenOperatorMeasure S hS) :
    IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection S) := by
  have heq := kernelRealDensity_eq_product_rnDeriv_toReal κ ν μ
  rw [hprod] at heq
  exact (isIntegralKernel_rnDeriv_integralBandProjection S hS).congr_ae
    (measurable_kernelRealDensity κ ν) heq.symm

theorem compProd_kernelSingularPart_eq_operator_residual
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hprod : μ ⊗ₘ κ = clopenOperatorMeasure S hS) :
    μ ⊗ₘ kernelSingularPart κ ν =
      clopenOperatorMeasure (S - integralBandProjection S)
        (sub_nonneg.mpr (integralBandProjection_le_id S hS)) := by
  rw [compProd_kernelSingularPart_eq_product_singularPart, hprod,
    clopenOperatorMeasure_singularBandPart]

theorem exists_positive_operator_kernel_parts (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    ∃ κ : Kernel X Y, IsFiniteKernel κ ∧
      (∀ x, κ x univ ≤ ENNReal.ofReal ‖S‖) ∧
      μ ⊗ₘ κ = clopenOperatorMeasure S hS ∧
      IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection S) := by
  obtain ⟨κ, hκ, hb, hprod, _⟩ := exists_positive_operator_kernel S hS
  letI := hκ
  exact ⟨κ, hκ, hb, hprod, isIntegralKernel_kernelRealDensity_of_operator S hS κ hprod⟩

end ThesisCommon
