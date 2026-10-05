import JLMS.HaglerJohnson
import JLMS.BlockFactorization
import JLMS.WeakStarFactorization

/-!
# The full original statements of Theorems 1.6 and 1.7

Both admissible-codomain alternatives now supply the quantitative projection
needed after the Section 6 and Section 7 disjoint-function constructions.
The no-ℓ¹ alternative uses the proved Hagler–Johnson normalized null blocks.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem factorizationFromDisjointFunctions :
    FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := X) := by
  intro hX T δ hδ hw
  rcases hX with hno | hseq
  · exact factorizationFromDisjointFunctions_of_blocks
      (dualNormalizedBlockNull_of_not_containsEllOne hno) T δ hδ hw
  · exact factorizationFromDisjointFunctions_weakStar hseq T δ hδ hw

theorem theorem_1_6 : Theorem_1_6 𝕜 K X := by
  intro hK hX
  rcases hX with hno | hseq
  · exact theorem_1_6_of_blocks (dualNormalizedBlockNull_of_not_containsEllOne hno) hK (Or.inl hno)
  · exact theorem_1_6_of_weakStar hseq hK (Or.inr hseq)

theorem theorem_1_7 : Theorem_1_7 𝕜 K X := by
  intro hK hX
  rcases hX with hno | hseq
  · exact theorem_1_7_of_blocks (dualNormalizedBlockNull_of_not_containsEllOne hno) hK (Or.inl hno)
  · exact theorem_1_7_of_weakStar hseq hK (Or.inr hseq)

end JLMS
