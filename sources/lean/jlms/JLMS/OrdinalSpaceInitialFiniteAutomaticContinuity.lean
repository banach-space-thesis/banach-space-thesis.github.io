import JLMS.OrdinalSpaceInitialFiniteReduction
import JLMS.OrdinalAutomaticContinuity

/-!
# Automatic continuity below the first countable multiple of a regular initial ordinal

The actual small-remainder and finite-power decompositions, together with
Ogden's theorem, prove Theorem 1.3 whenever κ≤α<κω and κ is a regular
uncountable initial ordinal. No classification theorem is assumed here.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]

theorem theorem_1_3_of_initial_finiteQuotient (c : Cardinal.{u})
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (α : Ordinal.{u})
    (hlo : c.ord ≤ α) (hhi : α < c.ord * Ordinal.omega0) :
    Theorem_1_3.{u, v, w} 𝕜 α :=
  theorem_1_3_of_classification α
    (ordinalSpaceReduction_of_initial_finiteQuotient c hc hu α hlo hhi)

end JLMS
