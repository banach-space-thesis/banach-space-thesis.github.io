import JLMS.OrdinalSpaceClassificationAssembly
import JLMS.OrdinalSpaceSingularReplication
import JLMS.OrdinalSpacePowerSquare

/-!
# The ordinal-space classification consequence used in Section 9

Every ordinal interval is finite, has a continuous-function space isomorphic
to its square, or has a continuous-function space isomorphic to a positive
finite power of the space on a regular uncountable initial ordinal.

Only this sufficient classification consequence is needed. Its ingredients
are the explicit interval splittings, endpoint-zero decompositions, Banach
c₀ sums, and the singular-initial and initial-power square constructions.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The actual classification consequence used in the proof of Theorem 1.3. -/
theorem ordinalSpaceReduction (α : Ordinal.{u}) : OrdinalSpaceReduction 𝕜 α :=
  ordinalSpaceReduction_of_initial_and_power_squares
    (fun c hc hs => ⟨ordinalSpaceSingularInitialSquareEquiv (𝕜 := 𝕜) c hc hs⟩)
    (fun c hc γ hγ hcard => ⟨ordinalSpaceInitialPowerSquareEquiv (𝕜 := 𝕜) c hc γ hγ hcard⟩)
    α

end JLMS
