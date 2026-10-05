import ThesisCommon.Analysis.ClopenOperatorMeasure
import ThesisCommon.Analysis.BoundedKernelDisintegration

/-! Reverse measurable kernels of positive L1 operators on the compact
zero-dimensional standard models. Both the product measure and its
disintegration are constructed; no random-measure representation is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

theorem exists_positive_operator_kernel (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) :
    ∃ κ : Kernel X Y, IsFiniteKernel κ ∧
      (∀ x, κ x univ ≤ ENNReal.ofReal ‖S‖) ∧
      μ ⊗ₘ κ = clopenOperatorMeasure S hS ∧
      ∀ (a : Set X) (b : Set Y) (ha : MeasurableSet a) (_hb : MeasurableSet b),
        (∫⁻ x in a, κ x b ∂μ) =
          ENNReal.ofReal (∫ y in b, S (lOneIndicator μ a ha) y ∂ν) := by
  obtain ⟨κ, hκ, hbound, hprod⟩ := exists_bounded_disintegration μ
    (clopenOperatorMeasure S hS) (norm_nonneg S) (clopenOperatorMeasure_fst_le S hS)
  letI := hκ
  refine ⟨κ, hκ, hbound, hprod, ?_⟩
  intro a b ha hb
  rw [← Measure.compProd_apply_prod ha hb, hprod, clopenOperatorMeasure_prod S hS ha hb]

end ThesisCommon
