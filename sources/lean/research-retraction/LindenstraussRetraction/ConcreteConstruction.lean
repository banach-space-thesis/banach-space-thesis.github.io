import LindenstraussRetraction.SummationSpace
import LindenstraussRetraction.Renorming
import LindenstraussRetraction.C0Sum
import LindenstraussRetraction.SchauderBasis

/-!
# The explicitly constructed spaces of Sections 4 and 5

These are the actual dependent direct sums and graph renormings used by the
paper, not existential stand-ins. The propositions below separate the statement
from its proof; NoSection, TwoSidedConstant and MainTheorem supply those proofs.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 512

namespace LindenstraussRetraction

universe v
variable (𝕜 : Type v) [RCLike 𝕜]

/-- Lean index `n` corresponds to the positive paper index `n+1`. -/
def coordinateScale (n : ℕ) : ℝ := (1/2 : ℝ) ^ (n+1)

theorem coordinateScale_pos (n : ℕ) : 0 < coordinateScale n := by
  exact pow_pos (by norm_num : (0 : ℝ) < 1/2) _

/-- The particular renormed spaces `Y_(n+1)` from Section 4. -/
abbrev RenormedSummationSpace (n : ℕ) : Type v :=
  AnisotropicSpace (summationOperator 𝕜) (coordinateScale n)

instance renormedSummationSpace_complete (n : ℕ) :
    CompleteSpace (RenormedSummationSpace 𝕜 n) := inferInstance

/-- The exact auxiliary space `W = (⊕ Y_n)_c₀` from Section 5. -/
abbrev AuxiliarySpace : Type v := C0Sum 𝕜 (RenormedSummationSpace 𝕜)

instance auxiliarySpace_complete : CompleteSpace (AuxiliarySpace 𝕜) := inferInstance

/-- `prop:no-section` for the explicit summation operator. -/
def SummationNoSectionStatement : Prop :=
  ¬ HasUniformSectionOnUnitBall (summationOperator 𝕜)

/-- `prop:auxiliary-space` for the specific constructed `W`.
This corrects the scope gap in the earlier existential summary target. -/
def ConcreteAuxiliarySpaceStatement : Prop :=
  Nonempty (MonotoneFDD 𝕜 (AuxiliarySpace 𝕜)) ∧
    ¬ HasUniformUnitBallBidualRetraction 𝕜 (AuxiliarySpace 𝕜)

/-- `prop:two-sided`, with positive indexing and real powers before coercion
to extended nonnegative reals. TwoSidedConstant proves this proposition. -/
def TwoSidedRetractionConstantStatement : Prop :=
  ∀ n : ℕ,
    ENNReal.ofReal ((2 : ℝ)^n) ≤
      bidualLipschitzRetractionConstant 𝕜 (RenormedSummationSpace 𝕜 n) ∧
    bidualLipschitzRetractionConstant 𝕜 (RenormedSummationSpace 𝕜 n) ≤
      ENNReal.ofReal ((2 : ℝ)^(n+1))

end LindenstraussRetraction
