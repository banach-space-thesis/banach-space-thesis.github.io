import SurveyStatements.P2OppositeShift
import SurveyStatements.P2MetricCardinality
import SurveyStatements.P2SimpleIso
import SurveyStatements.P2MatrixNonrepresentation

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open TopologicalSpace
namespace SurveyStatements.P2
universe v

/-- **Main result of Problem 2** (`p2:thm:main`). There is a unital complex
Banach algebra that is not Banach-algebra isomorphic to the Calkin algebra of
any complex Banach space.

The witness has carrier in `Type 0`, while `v` allows Banach spaces in any fixed
universe. There is no separability, nontriviality, or dimension restriction on
`X`. Thus a restriction on the universe size cannot supply the counterexample.
-/
theorem exists_non_calkin_unital_banach_algebra :
    ∃ A : ComplexBanachAlgebra.{0},
      ∀ (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
        ¬ Nonempty (CalkinBanachAlgebraIso X A.Carrier) := by
  refine ⟨oppositeShiftBanachAlgebra LargeAlphabet, ?_⟩
  intro X _ _ _
  rintro ⟨e⟩
  have hcard : Cardinal.continuum < Cardinal.mk X :=
    continuum_lt_mk_of_large_calkinIso X bethOmega_le_mk_oppositeShiftQuotient e
  have hnonseparable : ¬ SeparableSpace X :=
    not_separableSpace_of_continuum_lt_mk X hcard
  have hsimple : ∀ J : TwoSidedIdeal (Calkin X), J = ⊥ ∨ J = ⊤ :=
    CalkinBanachAlgebraIso.simple_of_simple X e (oppositeShiftQuotient_simple LargeAlphabet)
  exact false_of_oppositeShift_calkinIso X e hnonseparable hsimple

end SurveyStatements.P2

