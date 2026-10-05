import JLMS.OrdinalSpaceClassification
import JLMS.OrdinalAutomaticContinuity
import JLMS.CalkinNormUniqueness

/-!
# Theorem 1.3 and Corollary 1.4

The actual ordinal-space classification discharges the last input in the
Section 9 argument. Automatic continuity holds for every ordinal and every
Banach algebra target. Together with essential-norm minimality, it gives
uniqueness of algebra norms on both the operator and Calkin algebras.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]

/-- Every algebra homomorphism out of B(C[0,α]) into a Banach algebra is continuous. -/
theorem theorem_1_3 (α : Ordinal.{u}) : Theorem_1_3.{u, v, w} 𝕜 α :=
  theorem_1_3_of_classification α (ordinalSpaceReduction (𝕜 := 𝕜) α)

/-- Both B(C[0,α]) and its Calkin algebra have a unique algebra norm up to equivalence. -/
theorem corollary_1_4 (α : Ordinal.{u}) : Corollary_1_4 𝕜 α :=
  corollary_1_4_of_theorem_1_3 α (theorem_1_3 (𝕜 := 𝕜) α)

end JLMS
