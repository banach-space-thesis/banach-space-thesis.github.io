import NonCalkinAlgebra.QuotientAlgebra
import NonCalkinAlgebra.StatementLemmas

/-! Explicit outstanding proof targets. These definitions add no axioms and
do not assert that the targets have been proved.
-/
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u v

def IsTopologicallySimple (A : Type u) [NormedRing A] : Prop :=
  ∀ J : TwoSidedIdeal A, IsClosed (J : Set A) → J = ⊥ ∨ J = ⊤

/-- The Banach-algebra consequence needed from Theorem 2.2. The paper obtains
it from a simple unital AF C*-algebra. AF classification itself is not being
silently assumed or encoded as an additional axiom here.
-/
def CoefficientExistenceStatement : Prop :=
  ∃ D : ComplexBanachAlgebra.{0},
    ‖(1 : D.Carrier)‖ = 1 ∧
    HasDensityCharacter D.Carrier Cardinal.continuum ∧
    IsTopologicallySimple D.Carrier ∧
    ∀ (convention : QuotientConvention) (Y : Type v)
      [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
      [TopologicalSpace.SeparableSpace Y],
      ¬ Nonempty (OperatorQuotientIso Y convention D.Carrier)

/-- Lemma 2.4, simultaneously for both fixed choices of quotient ideal. -/
def IdempotentLiftingStatement : Prop :=
  ∀ (convention : QuotientConvention) (X : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : BoundedOperators X),
    T * T - T ∈ operatorIdeal X convention →
      ∃ P : BoundedOperators X, P * P = P ∧ P - T ∈ operatorIdeal X convention

end NonCalkinAlgebra
