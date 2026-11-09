import PL1.Definitions
import Mathlib.SetTheory.Cardinal.Continuum

noncomputable section

open scoped BigOperators

namespace PL1CD

abbrev ContinuumIndex := ℕ → Bool

abbrev L1Operator (𝕜 : Type) [RCLike 𝕜] :=
  PL1.IntervalL1 𝕜 →L[𝕜] PL1.IntervalL1 𝕜

def IsNormClosedTwoSidedIdeal (𝕜 : Type) [RCLike 𝕜]
    (I : Submodule 𝕜 (L1Operator 𝕜)) : Prop :=
  IsClosed (I : Set (L1Operator 𝕜)) ∧
  ∀ T ∈ I, ∀ U : L1Operator 𝕜, U.comp T ∈ I ∧ T.comp U ∈ I

def IsProperOperatorIdeal (𝕜 : Type) [RCLike 𝕜]
    (I : Submodule 𝕜 (L1Operator 𝕜)) : Prop :=
  I ≠ ⊤

def closedIdealGeneratedBy (𝕜 : Type) [RCLike 𝕜]
    (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) : Set (L1Operator 𝕜) :=
  closure {T | ∃ n : ℕ, ∃ a : Fin n → ContinuumIndex,
    (∀ j, a j ∈ S) ∧
    ∃ U V : Fin n → L1Operator 𝕜,
      T = ∑ j, (V j).comp ((P (a j)).comp (U j))}

def ClosedOperatorIdeals (𝕜 : Type) [RCLike 𝕜] :=
  {I : Submodule 𝕜 (L1Operator 𝕜) // IsNormClosedTwoSidedIdeal 𝕜 I}

def ClosedIdealCardinalityStatement (𝕜 : Type) [RCLike 𝕜] : Prop :=
  Cardinal.mk (ClosedOperatorIdeals 𝕜) =
    (2 : Cardinal) ^ Cardinal.continuum

def TheoremCSpec (𝕜 : Type) [RCLike 𝕜]
    (P : ContinuumIndex → L1Operator 𝕜) : Prop :=
  (∀ a, PL1.IsProjection (P a) ∧
    ‖P a‖ ≤ PL1.projectionBound ∧
    IsClosed ((P a).range : Set (PL1.IntervalL1 𝕜))) ∧
  ∀ a b, a ≠ b →
    ¬ PL1.ContainsIsomorphicCopy 𝕜 (P a).range (P b).range

def TheoremCStatement (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∃ P : ContinuumIndex → L1Operator 𝕜, TheoremCSpec 𝕜 P

def TheoremCAdditionalStrongSpec (𝕜 : Type) [RCLike 𝕜]
    (P : ContinuumIndex → L1Operator 𝕜) : Prop :=
  ∀ a, ¬ FiniteDimensional 𝕜 (P a).range ∧
    PL1.HasSchurProperty 𝕜 (P a).range ∧
    ¬ @PL1.HasRadonNikodymProperty.{_, 0} (PL1.UnderlyingReal 𝕜 (P a).range)
        (inferInstanceAs (NormedAddCommGroup (P a).range))
        (NormedSpace.restrictScalars ℝ 𝕜 (P a).range) ∧
    ¬ @PL1.HasEquivalentRealLatticeNorm (PL1.UnderlyingReal 𝕜 (P a).range)
        (inferInstanceAs (NormedAddCommGroup (P a).range))
        (NormedSpace.restrictScalars ℝ 𝕜 (P a).range)

def TheoremDOrderSpec (𝕜 : Type) [RCLike 𝕜]
    (J : Set ContinuumIndex → Submodule 𝕜 (L1Operator 𝕜)) : Prop :=
  (∀ S, IsNormClosedTwoSidedIdeal 𝕜 (J S) ∧ IsProperOperatorIdeal 𝕜 (J S)) ∧
  ∀ S T, J S ≤ J T ↔ S ⊆ T

def TheoremDStatement (𝕜 : Type) [RCLike 𝕜] : Prop :=
  (∃ J : Set ContinuumIndex → Submodule 𝕜 (L1Operator 𝕜),
    TheoremDOrderSpec 𝕜 J) ∧
  ClosedIdealCardinalityStatement 𝕜

def TheoremDAdditionalSpec (𝕜 : Type) [RCLike 𝕜]
    (P : ContinuumIndex → L1Operator 𝕜)
    (J : Set ContinuumIndex → Submodule 𝕜 (L1Operator 𝕜)) : Prop :=
  (∀ S, (J S : Set (L1Operator 𝕜)) = closedIdealGeneratedBy 𝕜 P S) ∧
  (∀ S, ∀ T ∈ J S, PL1.IsDunfordPettis T) ∧
  (J ∅ = ⊥) ∧
  ∀ S, S.Nonempty → ∃ a ∈ S,
    P a ∈ J S ∧ PL1.IsProjection (P a) ∧ ¬ FiniteDimensional 𝕜 (P a).range

def TheoremsCDStrongStatement (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∃ P : ContinuumIndex → L1Operator 𝕜,
    ∃ J : Set ContinuumIndex → Submodule 𝕜 (L1Operator 𝕜),
      TheoremCSpec 𝕜 P ∧
      TheoremCAdditionalStrongSpec 𝕜 P ∧
      TheoremDOrderSpec 𝕜 J ∧
      TheoremDAdditionalSpec 𝕜 P J ∧
      ClosedIdealCardinalityStatement 𝕜

def TheoremCRealStatement : Prop := TheoremCStatement ℝ

def TheoremCComplexStatement : Prop := TheoremCStatement ℂ

def TheoremDRealStatement : Prop := TheoremDStatement ℝ

def TheoremDComplexStatement : Prop := TheoremDStatement ℂ

def TheoremsCDRealStrongStatement : Prop := TheoremsCDStrongStatement ℝ

def TheoremsCDComplexStrongStatement : Prop := TheoremsCDStrongStatement ℂ

end PL1CD
