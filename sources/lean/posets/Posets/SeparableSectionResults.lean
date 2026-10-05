import Posets.CountableOrdinalIdealResults
import Posets.AlspachCounterexampleNonfactorization
import Posets.SeparableIdealCounterexampleReduction
import Posets.SeparableMetrizable

/-! Exact remaining separable operator-ideal results of the paper. The
Alspach operator is a concrete surjection with proved nonfactorisation;
the ordinal primary factorisation input is proved independently. -/

noncomputable section
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem proposition_3_4_proof : Proposition_3_4 𝕜 :=
  proposition_3_4_of_counterexample ordinalOmegaOmegaSq_hasPFP
    alspachOrdinalOperator alspachOrdinalOperator_surjective
    alspachOrdinalOperator_doesNotFactorIdentity

/-- As usual, the compact space is nonempty; the formal target includes
that convention explicitly. -/
theorem proposition_1_10_proof : Proposition_1_10 𝕜 :=
  proposition_1_10_of_section_3 corollary_3_3 proposition_3_4_proof

end Posets
