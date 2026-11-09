import NonCalkinAlgebra.OperatorIdeals
import Mathlib.SetTheory.Cardinal.Continuum

/-! Literal targets from arXiv:2607.15075v1. These are propositions, not
unproved theorems or additional axioms. Proof status is tracked separately.
-/

set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u v

/-- `κ` is the least cardinality of a dense subset, with its minimum attained. -/
def HasDensityCharacter (A : Type u) [TopologicalSpace A] (κ : Cardinal.{u}) : Prop :=
  (∃ S : Set A, Dense S ∧ Cardinal.mk S = κ) ∧
    ∀ S : Set A, Dense S → κ ≤ Cardinal.mk S

def IsNonzeroProperClosedIdeal {A : Type u} [NormedRing A] (J : TwoSidedIdeal A) : Prop :=
  IsClosed (J : Set A) ∧ J ≠ ⊥ ∧ J ≠ ⊤

def HasExactlyOneNonzeroProperClosedIdeal (A : Type u) [NormedRing A] : Prop :=
  ∃! J : TwoSidedIdeal A, IsNonzeroProperClosedIdeal J

/-- Theorem 1.1: one and the same continuum-density witness for both conventions,
with its exact closed-ideal condition and no separability restriction on `X`.
The space universe `v` is arbitrary; the witness is in `Type 0`.
-/
def MainStatement : Prop :=
  ∃ A : ComplexBanachAlgebra.{0},
    HasDensityCharacter A.Carrier Cardinal.continuum ∧
    HasExactlyOneNonzeroProperClosedIdeal A.Carrier ∧
    ∀ (convention : QuotientConvention) (X : Type v)
      [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
      ¬ Nonempty (OperatorQuotientIso X convention A.Carrier)

end NonCalkinAlgebra
