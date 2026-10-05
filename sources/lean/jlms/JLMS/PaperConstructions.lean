import JLMS.Rudin
import JLMS.SectionEightAssembly

/-!
# Paper constructions with Rudin's theorem discharged

Theorem 3.3 and the sharper Section 7 construction now follow from their
original hypotheses. The main factorization and norm theorems still depend
on the separately stated cited bridge and Section 8 background inputs.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Theorem 3.3, from the paper's original hypotheses. -/
theorem disjointFunctionsHalf : DisjointFunctionsHalf (𝕜 := 𝕜) (K := K) (X := X) :=
  disjointFunctionsHalf_of_rudin rudinRepresentation

/-- The stronger Section 7 construction, from the original hypotheses. -/
theorem disjointFunctionsSharp : DisjointFunctionsSharp (𝕜 := 𝕜) (K := K) (X := X) :=
  disjointFunctionsSharp_of_rudin rudinRepresentation

/-- Only the cited factorization bridge remains for Theorem 1.6. -/
theorem theorem_1_6_of_bridge
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := X)) :
    Theorem_1_6 𝕜 K X := theorem_1_6_of_rudin_and_bridge rudinRepresentation hbridge

/-- Only the cited factorization bridge remains for Theorem 1.7. -/
theorem theorem_1_7_of_bridge
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := X)) :
    Theorem_1_7 𝕜 K X := theorem_1_7_of_rudin_and_bridge rudinRepresentation hbridge

end JLMS
