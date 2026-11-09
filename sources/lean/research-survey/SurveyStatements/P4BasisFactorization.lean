import SurveyStatements.P4Approximation
import SurveyStatements.P4ConvexTails
import SurveyStatements.P4WeakMetric
import SurveyStatements.P4BidualApproximation
import SurveyStatements.P4FactorizationCalculus
import SurveyStatements.P4DFJPOperatorFactorization
import SurveyStatements.P4Lp2Reflexivity
import SurveyStatements.P4FinitePath
import SurveyStatements.P4PeriodicFiniteSums
import SurveyStatements.P4BasisFactorizationAssembly

noncomputable section
set_option autoImplicit false

universe u v w

namespace SurveyStatements.P4

variable (𝕜 : Type u) [RCLike 𝕜]

/-- **Problem 4, main theorem** (`p5:thm:main` in the supplied source).
Every weakly compact operator into a separable Banach space with the bounded
approximation property factors through a reflexive Banach space with a
Schauder basis. The proof combines actual two-sided finite-rank approximants,
the invariant weakly compact convergent-sequence bridge, DFJP interpolation,
and the complemented Schauder-basis extension of its finite decomposition. -/
theorem weaklyCompact_basis_factorization
    {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y]
    (hBAP : HasBoundedApproximationProperty 𝕜 Y)
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T) :
    FactorsThroughReflexiveBasisSpace 𝕜 T := by
  exact weaklyCompact_basis_factorization_assembled hBAP T hT

end SurveyStatements.P4

