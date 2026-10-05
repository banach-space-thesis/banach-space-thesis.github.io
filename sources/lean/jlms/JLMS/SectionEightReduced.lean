import JLMS.SectionEightConclusions
import JLMS.CZeroAdmissibility

/-!
# Section 8 with all inputs except the factorization bridge discharged

Rudin, the norm-one retract, C₀(K) admissibility, the simultaneous series,
and complete uniqueness are constructed. The sole remaining input to these
original main statements is the cited general-codomain factorization bridge.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

theorem theorem_1_1_of_bridge
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := CZero 𝕜 K)) :
    Theorem_1_1 𝕜 K := by
  intro hK
  exact theorem_1_1_of_bridge_admissible hbridge (cZero_admissible hK) hK

theorem theorem_1_5_of_bridge
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := CZero 𝕜 K)) :
    Theorem_1_5 𝕜 K := by
  intro hK
  exact theorem_1_5_of_bridge_admissible hbridge (cZero_admissible hK) hK

end JLMS
