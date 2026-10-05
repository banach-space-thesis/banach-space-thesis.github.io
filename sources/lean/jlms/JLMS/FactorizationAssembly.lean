import JLMS.DisjointConstruction

/-!
# Theorems 1.6 and 1.7 from the two external analytic inputs

The entire paper-specific construction in Sections 4–7 is now implemented.
Only Rudin's representation and the cited Arnott–Laustsen/Hagler–Johnson bridge
remain explicit inputs here. Positivity of the dual essential norm for Theorem
1.7 follows from the already obtained factorization in Theorem 1.6.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem theorem_1_6_of_rudin_and_bridge (hRudin : RudinRepresentation 𝕜 K)
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := X)) :
    Theorem_1_6 𝕜 K X :=
  theorem_1_6_of_disjointFunctions (disjointFunctionsHalf_of_rudin hRudin) hbridge

theorem theorem_1_7_of_rudin_and_bridge (hRudin : RudinRepresentation 𝕜 K)
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := X)) :
    Theorem_1_7 𝕜 K X := by
  intro hK hX T hT
  obtain ⟨U, V, hfactor, _⟩ := theorem_1_6_of_rudin_and_bridge hRudin hbridge hK hX T hT 1 zero_lt_one
  have hpositive := dualEssentialNorm_pos_of_cZero_factorization T U V hfactor
  have hsharp := sharpFactorizations_of_disjointFunctions
    (disjointFunctionsSharp_of_rudin hRudin) hbridge hK hX T
  exact factorizationValues_isLUB_of_sharp_cZero T hpositive hsharp

end JLMS
