import LindenstraussRetraction.BimonotoneRenorm
import LindenstraussRetraction.BasisSeparability
import LindenstraussRetraction.ComplementedTransfer

/-! The final transfer from a concrete bounded Schauder basis counterexample.
This reduction does not assert that its input witness exists. -/

noncomputable section
namespace LindenstraussRetraction

variable {𝕜 : Type} [RCLike 𝕜] [TopologicalSpace.SeparableSpace 𝕜]
variable {X : Type} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem mainStatement_of_boundedBasis_counterexample
    (b : SchauderBasis 𝕜 X) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ N, ‖b.partialSum N‖ ≤ B)
    (hno : ¬ HasUniformUnitBallBidualRetraction 𝕜 X) : MainStatement 𝕜 := by
  letI : TopologicalSpace.SeparableSpace X := b.separableSpace
  let Z := BimonotoneSpace b B hB hP
  letI : TopologicalSpace.SeparableSpace Z := bimonotoneSpace_separable b B hB hP
  have hnoZ : ¬ HasUniformUnitBallBidualRetraction 𝕜 Z := by
    intro h
    apply hno
    exact (hasUniformUnitBallBidualRetraction_iff_of_continuousLinearEquiv 𝕜
      (bimonotoneEquiv b B hB hP)).mpr h
  apply mainUnitBallStatement_implies_mainStatement 𝕜
  refine ⟨{ Carrier := Z }, ?_, hnoZ⟩
  exact ⟨bimonotoneBasis b B hB hP, bimonotoneBasis_isBimonotone b B hB hP⟩

end LindenstraussRetraction
