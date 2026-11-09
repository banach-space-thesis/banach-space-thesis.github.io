import SurveyStatements.P5VectorPartitionNatural
import SurveyStatements.P5Support.LpPartitionTransfer

/-! Exact compatibility with scalar partition transport. Thus scalar
faithful-tree identities can be carried to genuine Bochner tensors. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5

variable {𝕜 α ι : Type*} [RCLike 𝕜] [MeasurableSpace α] [Fintype ι]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]

theorem finiteLpIntegral_scalar (hp : p ≠ ∞) :
    finiteLpIntegral (𝕜 := 𝕜) (E := 𝕜) (μ := μ) hp =
      P5Support.lpHaarFiniteIntegral (𝕜 := 𝕜) (μ := μ) hp := by
  apply ContinuousLinearMap.ext
  intro f
  rw [finiteLpIntegral_apply, P5Support.lpHaarFiniteIntegral_apply]
  change (@integral α 𝕜 _ (NormedSpace.restrictScalars ℝ 𝕜 𝕜)
    _ μ (fun x => f x)) = ∫ x, f x ∂μ
  rw [NormedSpace.restrictScalars_eq]

theorem vectorLpPartitionAverage_scalar (hp : p ≠ ∞) (s : Set α) :
    vectorLpPartitionAverage (𝕜 := 𝕜) (E := 𝕜) (μ := μ) hp s =
      P5Support.lpHaarPartitionAverage (𝕜 := 𝕜) (μ := μ) hp s := by
  unfold vectorLpPartitionAverage P5Support.lpHaarPartitionAverage
  rw [finiteLpIntegral_scalar]

theorem vectorLpPartitionTransfer_scalar (hp : p ≠ ∞) (s t : ι → Set α)
    (ht : ∀ i, MeasurableSet (t i)) :
    vectorLpPartitionTransfer (𝕜 := 𝕜) (E := 𝕜) (μ := μ) hp s t ht =
      P5Support.lpHaarPartitionTransfer (𝕜 := 𝕜) (μ := μ) hp s t ht := by
  apply ContinuousLinearMap.ext
  intro f
  rw [vectorLpPartitionTransfer_apply, P5Support.lpHaarPartitionTransfer_apply]
  unfold vectorLpPartitionStep P5Support.lpHaarPartitionStep
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [vectorLpPartitionAverage_scalar]

end SurveyStatements.P5
