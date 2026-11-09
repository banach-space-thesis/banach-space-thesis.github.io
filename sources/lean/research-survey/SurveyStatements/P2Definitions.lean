import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Group.Quotient

set_option autoImplicit false

/-!
# Problem 2: unital complex Banach algebras that are not Calkin algebras

Source: `source/problems/P2-non-unital-calkin-algebra.tex`, theorem
`p2:thm:main`. Despite the source filename, the algebra in the theorem is unital.

The Calkin space below is the actual quotient by compact operators, with mathlib's
quotient norm and topology. Its multiplicative structure is specified on quotient
representatives in `CalkinBanachAlgebraIso`: `[S] * [T] = [S * T]` and `1 = [id]`.
This avoids requiring a separate implementation of all noncommutative quotient
ring instances just to state the result. The linear equivalence and its inverse
are continuous, hence bounded; thus this is exactly a Banach-algebra isomorphism,
not merely an algebraic or a linear isomorphism.
-/

namespace SurveyStatements.P2

universe u v

/-- A nonzero unital complex Banach algebra. Multiplication need not commute. -/
structure ComplexBanachAlgebra where
  Carrier : Type u
  [normedRing : NormedRing Carrier]
  [normedAlgebra : NormedAlgebra ℂ Carrier]
  [completeSpace : CompleteSpace Carrier]
  [nontrivial : Nontrivial Carrier]

attribute [instance] ComplexBanachAlgebra.normedRing
  ComplexBanachAlgebra.normedAlgebra ComplexBanachAlgebra.completeSpace
  ComplexBanachAlgebra.nontrivial

section Calkin

variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The algebra `B(X)` of bounded complex-linear endomorphisms, in operator norm. -/
abbrev BoundedOperators := X →L[ℂ] X

/-- The subspace `K(X)` of compact operators. Compact means that the image of the
closed unit ball has compact closure (equivalently, mathlib's `IsCompactOperator`).
It is a two-sided ideal for composition. -/
abbrev CompactOperators : Submodule ℂ (BoundedOperators X) :=
  compactOperator (RingHom.id ℂ) X X

/-- Compact operators form a closed subspace when the target is complete. -/
instance compactOperators_isClosed [CompleteSpace X] :
    IsClosed (CompactOperators X : Set (BoundedOperators X)) :=
  isClosed_setOf_isCompactOperator

/-- The Calkin quotient `B(X) / K(X)`, with its quotient norm and topology. -/
abbrev Calkin := BoundedOperators X ⧸ CompactOperators X

/-- The quotient map `T ↦ T + K(X)`. -/
def calkinQuotient (T : BoundedOperators X) : Calkin X :=
  Submodule.Quotient.mk T

/-- A Banach-algebra isomorphism `B(X) / K(X) ≅ A`.

Preservation of multiplication and the unit is expressed on representatives;
every Calkin element has such a representative. `S * T` is operator composition.
The inherited equivalence includes complex linearity, continuity in both
directions, and bijectivity. No norm preservation is required.
-/
structure CalkinBanachAlgebraIso (A : Type u) [NormedRing A]
    [NormedAlgebra ℂ A] extends Calkin X ≃L[ℂ] A where
  map_mul_representatives : ∀ S T : BoundedOperators X,
    toContinuousLinearEquiv (calkinQuotient X (S * T)) =
      toContinuousLinearEquiv (calkinQuotient X S) *
        toContinuousLinearEquiv (calkinQuotient X T)
  map_one_representative :
    toContinuousLinearEquiv (calkinQuotient X 1) = 1

end Calkin

end SurveyStatements.P2

