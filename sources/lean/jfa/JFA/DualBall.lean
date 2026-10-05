import JFA.CountableDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! The weak-star dual unit ball of a separable normed space is compact and
second countable. Dense-vector evaluations give an explicit embedding into
the countable product of the scalar field. -/

noncomputable section
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

abbrev DualBall (𝕜 F : Type*) [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  {φ : WeakDual 𝕜 F // φ ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 F) 1}

instance dualBallCompactSpace : CompactSpace (DualBall 𝕜 F) :=
  isCompact_iff_compactSpace.mp
    (WeakDual.isCompact_closedBall 𝕜 (E := F) (0 : StrongDual 𝕜 F) 1)

variable [SeparableSpace F]

def dualBallCoordinates (φ : DualBall 𝕜 F) (n : ℕ) : 𝕜 := φ.val (denseSeq F n)

theorem continuous_dualBallCoordinates : Continuous (dualBallCoordinates (𝕜 := 𝕜) (F := F)) := by
  apply continuous_pi
  intro n
  exact (WeakDual.eval_continuous (denseSeq F n)).comp continuous_subtype_val

theorem dualBallCoordinates_injective :
    Function.Injective (dualBallCoordinates (𝕜 := 𝕜) (F := F)) := by
  intro φ ψ h
  apply Subtype.ext
  apply WeakDual.toStrongDual.injective
  apply ContinuousLinearMap.coeFn_injective
  apply (denseRange_denseSeq F).equalizer
    (WeakDual.toStrongDual φ.val).continuous (WeakDual.toStrongDual ψ.val).continuous
  funext n
  exact congrFun h n

theorem dualBallCoordinates_isClosedEmbedding :
    Topology.IsClosedEmbedding (dualBallCoordinates (𝕜 := 𝕜) (F := F)) :=
  continuous_dualBallCoordinates.isClosedEmbedding dualBallCoordinates_injective

instance dualBallSecondCountableTopology : SecondCountableTopology (DualBall 𝕜 F) :=
  dualBallCoordinates_isClosedEmbedding.isEmbedding.secondCountableTopology

end JFA
