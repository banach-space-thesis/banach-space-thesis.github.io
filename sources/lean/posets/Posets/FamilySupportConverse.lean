import Posets.FamilySupport
import PosetsCommon.CZeroRestriction

noncomputable section
open ThesisCommon Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

/-- Countable family support suffices even without closedness of the subspace. -/
theorem separable_of_familySupportSet_countable (h𝒜 : IsAlmostDisjoint 𝒜)
    (X : Submodule 𝕜 (Space 𝕜 𝒜))
    (hcount : (familySupportSet 𝕜 (X : Set (Space 𝕜 𝒜))).Countable) :
    TopologicalSpace.SeparableSpace X := by
  let ℬ : Set (Set ℕ) := Subtype.val '' familySupportSet 𝕜 (X : Set (Space 𝕜 𝒜))
  have hsub : ℬ ⊆ 𝒜 := by rintro _ ⟨A, _, rfl⟩; exact A.property
  have hℬ : IsAlmostDisjoint ℬ :=
    ⟨fun A hA => h𝒜.1 A (hsub hA), fun A hA B hB hAB => h𝒜.2 A (hsub hA) B (hsub hB) hAB⟩
  have hBcount : ℬ.Countable := hcount.image Subtype.val
  letI : Countable ℬ := hBcount.to_subtype
  letI : Countable (Mrowka ℬ) := inferInstanceAs (Countable (ℕ ⊕ ℬ))
  letI := mrowka_t2 ℬ hℬ
  letI := mrowka_locallyCompact ℬ hℬ
  apply supportedSubmodule_separable (pointInclusion hsub)
    (pointInclusion_isOpenEmbedding hsub).isEmbedding X
  intro f p hp
  cases p with
  | inl n => exact False.elim (hp ⟨Sum.inl n, rfl⟩)
  | inr A =>
    by_contra hne
    have hA : A.val ∈ ℬ := ⟨A, ⟨f.val, f.property, hne⟩, rfl⟩
    apply hp
    refine ⟨Sum.inr ⟨A.val, hA⟩, ?_⟩
    rfl

theorem lemma_4_3_proof (𝕜 : Type) [RCLike 𝕜] (𝒜 : Set (Set ℕ)) : Lemma_4_3 𝕜 𝒜 := by
  intro h𝒜 X _
  constructor
  · intro hsep
    letI := hsep
    exact familySupportSet_countable_of_separable (X : Set (Space 𝕜 𝒜))
  · exact separable_of_familySupportSet_countable h𝒜 X

end Posets
