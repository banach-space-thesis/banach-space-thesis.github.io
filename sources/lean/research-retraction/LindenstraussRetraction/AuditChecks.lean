import LindenstraussRetraction.NoSection
import LindenstraussRetraction.AuxiliaryNoRetraction
import LindenstraussRetraction.RenormedRetractionObstruction
import LindenstraussRetraction.MainFromBasis
import LindenstraussRetraction.MainTheorem

/-!
# Concrete semantic and axiom checks

These examples consume proved theorem terms, including expanded retraction
definitions with their actual canonical inclusions. They do not assert a
statement by defining a proposition or assume the conclusions being checked.
-/

noncomputable section

open scoped ENNReal

namespace LindenstraussRetraction.AuditChecks

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

-- Give instance search the standard graph and c₀-subspace instances directly.
-- This changes no norm or topology; it avoids an expensive search through the
-- nested dependent submodules when spelling out the bidual function type.
local instance auditRenormedNormedSpace (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    NormedSpace 𝕜 (RenormedSummationSpace 𝕜 n) :=
  Submodule.normedSpace (𝕜 := 𝕜) (R := 𝕜) (E := SummationSpace 𝕜 × C0 𝕜)
    (AnisotropicSpace (summationOperator 𝕜) (coordinateScale n))

local instance auditAuxiliaryNormedSpace (𝕜 : Type) [RCLike 𝕜] :
    NormedSpace 𝕜 (AuxiliarySpace 𝕜) :=
  Submodule.normedSpace (𝕜 := 𝕜) (R := 𝕜) (E := lp (RenormedSummationSpace 𝕜) ∞)
    (c0SumSubmodule 𝕜 (RenormedSummationSpace 𝕜))

example : ¬ HasUniformSectionOnUnitBall (summationOperator ℝ) :=
  no_uniformSection_summationOperator ℝ

example : ¬ HasUniformSectionOnUnitBall (summationOperator ℂ) :=
  no_uniformSection_summationOperator ℂ

example : ¬ ∃ s : UnitBall (C0 ℝ) → SummationSpace ℝ,
    UniformContinuous s ∧ ∀ x, summationOperator ℝ (s x) = x.val :=
  no_uniformSection_summationOperator ℝ

example : ¬ ∃ s : UnitBall (C0 ℂ) → SummationSpace ℂ,
    UniformContinuous s ∧ ∀ x, summationOperator ℂ (s x) = x.val :=
  no_uniformSection_summationOperator ℂ

example : ¬ HasUniformUnitBallBidualRetraction ℝ (AuxiliarySpace ℝ) :=
  no_uniformUnitBallRetraction_auxiliarySpace ℝ

example : ¬ HasUniformUnitBallBidualRetraction ℂ (AuxiliarySpace ℂ) :=
  no_uniformUnitBallRetraction_auxiliarySpace ℂ

example : ¬ ∃ r : UnitBall (Bidual ℝ (AuxiliarySpace ℝ)) → UnitBall (AuxiliarySpace ℝ),
    UniformContinuous r ∧
      Function.LeftInverse r (unitBallBidualEmbedding ℝ (AuxiliarySpace ℝ)) :=
  no_uniformUnitBallRetraction_auxiliarySpace ℝ

example : ¬ ∃ r : UnitBall (Bidual ℂ (AuxiliarySpace ℂ)) → UnitBall (AuxiliarySpace ℂ),
    UniformContinuous r ∧
      Function.LeftInverse r (unitBallBidualEmbedding ℂ (AuxiliarySpace ℂ)) :=
  no_uniformUnitBallRetraction_auxiliarySpace ℂ

example : coordinateScale 0 = (1 / 2 : ℝ) := by
  norm_num [coordinateScale]

example : coordinateScale 1 = (1 / 4 : ℝ) := by
  norm_num [coordinateScale]

example (x : C0 ℝ) :
    bidualMap (summationOperator ℝ) (summationBidualLift ℝ x) =
      bidualEmbedding ℝ (C0 ℝ) x := summationBidualLift_rightInverse ℝ x

example (x : C0 ℂ) :
    bidualMap (summationOperator ℂ) (summationBidualLift ℂ x) =
      bidualEmbedding ℂ (C0 ℂ) x := summationBidualLift_rightInverse ℂ x

example (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (b : SchauderBasis ℝ X) (hP : ∀ N, ‖b.partialSum N‖ ≤ 3)
    (hno : ¬ HasUniformUnitBallBidualRetraction ℝ X) : MainStatement ℝ :=
  mainStatement_of_boundedBasis_counterexample b 3 (by norm_num) hP hno

example (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (b : SchauderBasis ℂ X) (hP : ∀ N, ‖b.partialSum N‖ ≤ 3)
    (hno : ¬ HasUniformUnitBallBidualRetraction ℂ X) : MainStatement ℂ :=
  mainStatement_of_boundedBasis_counterexample b 3 (by norm_num) hP hno

-- These are unconditional existence proofs, using the completed concrete
-- construction. The fully expanded versions keep all conclusions on one X.
example : MainStatement ℝ := main_real

example : MainStatement ℂ := main_complex

example : ∃ X : SeparableBanachSpace.{0, 0} ℝ,
    (∃ b : SchauderBasis ℝ X.Carrier,
      (∀ N, ‖b.partialSum N‖ ≤ 1) ∧
        ∀ N, ‖ContinuousLinearMap.id ℝ X.Carrier - b.partialSum N‖ ≤ 1) ∧
    (¬ ∃ r : UnitBall (Bidual ℝ X.Carrier) → UnitBall X.Carrier,
      UniformContinuous r ∧ ∀ x, r (unitBallBidualEmbedding ℝ X.Carrier x) = x) ∧
    (¬ ∃ r : Bidual ℝ X.Carrier → X.Carrier,
      UniformContinuous r ∧ ∀ x, r (bidualEmbedding ℝ X.Carrier x) = x) ∧
    (¬ ∃ (K : NNReal) (r : Bidual ℝ X.Carrier → X.Carrier),
      LipschitzWith K r ∧ ∀ x, r (bidualEmbedding ℝ X.Carrier x) = x) := main_real

example : ∃ X : SeparableBanachSpace.{0, 0} ℂ,
    (∃ b : SchauderBasis ℂ X.Carrier,
      (∀ N, ‖b.partialSum N‖ ≤ 1) ∧
        ∀ N, ‖ContinuousLinearMap.id ℂ X.Carrier - b.partialSum N‖ ≤ 1) ∧
    (¬ ∃ r : UnitBall (Bidual ℂ X.Carrier) → UnitBall X.Carrier,
      UniformContinuous r ∧ ∀ x, r (unitBallBidualEmbedding ℂ X.Carrier x) = x) ∧
    (¬ ∃ r : Bidual ℂ X.Carrier → X.Carrier,
      UniformContinuous r ∧ ∀ x, r (bidualEmbedding ℂ X.Carrier x) = x) ∧
    (¬ ∃ (K : NNReal) (r : Bidual ℂ X.Carrier → X.Carrier),
      LipschitzWith K r ∧ ∀ x, r (bidualEmbedding ℂ X.Carrier x) = x) := main_complex

#print axioms no_uniformSection_summationOperator
#print axioms no_uniformUnitBallRetraction_auxiliarySpace
#print axioms norm_renormedBidualLift_le
#print axioms exists_sphereApproximation_of_renormedRetraction
#print axioms no_commonRenormedBallRetractions
#print axioms mainStatement_of_boundedBasis_counterexample
#print axioms mainTheorem
#print axioms main_real
#print axioms main_complex
#print axioms concreteAuxiliarySpaceTheorem

end LindenstraussRetraction.AuditChecks
