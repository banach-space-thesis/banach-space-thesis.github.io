import Posets.MrowkaIndicators
import Posets.ReducedMatrixBound
import JFA.CountableMrowkaTails
import JFA.DisjointCZeroSynthesis

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

def familyTailVector (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) (G : Finset ℕ) : Space 𝕜 𝒜 :=
  JLMS.clopenIndicator (JFA.mrowkaNeighborhood 𝒜 A G)
    (JFA.mrowka_isClopen_neighborhood h𝒜 A G) (JFA.mrowka_isCompact_neighborhood A G)

@[simp] theorem familyTailVector_natural (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) (G : Finset ℕ) (k : ℕ) :
    familyTailVector (𝕜 := 𝕜) h𝒜 A G (Sum.inl k) = if k ∈ A.val ∧ k ∉ G then 1 else 0 := by
  simp [familyTailVector, JLMS.clopenIndicator_apply, JFA.mrowkaNeighborhood, JFA.Mrowka]

@[simp] theorem familyTailVector_family (h𝒜 : IsAlmostDisjoint 𝒜) (A B : 𝒜) (G : Finset ℕ) :
    familyTailVector (𝕜 := 𝕜) h𝒜 A G (Sum.inr B) = if B = A then 1 else 0 := by
  simp [familyTailVector, JLMS.clopenIndicator_apply, JFA.mrowkaNeighborhood, JFA.Mrowka]

theorem familyTailVector_eq (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) (G : Finset ℕ) :
    familyTailVector (𝕜 := 𝕜) h𝒜 A G = familyVector 𝕜 𝒜 h𝒜 A -
      ∑ n ∈ G.filter (· ∈ A.val), isolatedVector 𝕜 𝒜 n := by
  ext p
  rw [ZeroAtInftyContinuousMap.sub_apply, czero_finset_sum_apply]
  cases p with
  | inl k =>
    simp only [familyTailVector_natural, familyVector_natural, isolatedVector_natural]
    rw [Finset.sum_ite_eq]
    by_cases hA : k ∈ A.val <;> by_cases hG : k ∈ G <;> simp [indicator, hA, hG]
  | inr B => simp only [familyTailVector_family, familyVector_family,
      isolatedVector_family, Finset.sum_const_zero, sub_zero]

theorem norm_familyTailVector_le (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) (G : Finset ℕ) :
    ‖familyTailVector (𝕜 := 𝕜) h𝒜 A G‖ ≤ 1 := JLMS.norm_clopenIndicator_le _ _ _

theorem familyTailVector_support_subset (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) (G : Finset ℕ) :
    Function.support (familyTailVector (𝕜 := 𝕜) h𝒜 A G) ⊆ JFA.mrowkaNeighborhood 𝒜 A G := by
  intro p hp
  by_contra h
  exact hp (by simp [familyTailVector, JLMS.clopenIndicator_apply, h])

theorem functional_familyTailVector {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h𝒜 : IsAlmostDisjoint 𝒜) (φ : Space 𝕜 𝒜 →L[𝕜] F)
    (hz : ∀ n, φ (isolatedVector 𝕜 𝒜 n) = 0) (A : 𝒜) (G : Finset ℕ) :
    φ (familyTailVector h𝒜 A G) = φ (familyVector 𝕜 𝒜 h𝒜 A) := by
  rw [familyTailVector_eq, map_sub, map_sum]
  simp only [hz, Finset.sum_const_zero, sub_zero]

end Posets
