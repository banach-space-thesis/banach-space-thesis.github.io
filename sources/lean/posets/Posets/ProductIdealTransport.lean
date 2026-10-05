import Posets.ProductIdealMaximal

/-! Transport of genuine closed ideals under bounded multiplicative linear
equivalences. No preservation of a unit is needed. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 A B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Mul B]

def closedIdealLinearEquivOrderIso (e : A ≃L[𝕜] B)
    (hmul : ∀ a b, e (a * b) = e a * e b) :
    ClosedIdeal 𝕜 A ≃o ClosedIdeal 𝕜 B where
  toFun I := ⟨e '' I.val, by
    refine ⟨e.toHomeomorph.isClosedMap _ I.property.1, ⟨0, I.property.2.1, map_zero e⟩,
      ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a + b, I.property.2.2.1 _ ha _ hb, map_add e a b⟩
    · rintro c _ ⟨a, ha, rfl⟩
      exact ⟨c • a, I.property.2.2.2.1 c _ ha, map_smul e c a⟩
    · rintro a _ ⟨b, hb, rfl⟩
      obtain ⟨a, rfl⟩ := e.surjective a
      exact ⟨⟨a * b, (I.property.2.2.2.2 a b hb).1, hmul a b⟩,
        ⟨b * a, (I.property.2.2.2.2 a b hb).2, hmul b a⟩⟩⟩
  invFun J := ⟨e ⁻¹' J.val, by
    refine ⟨J.property.1.preimage e.continuous, ?_, ?_, ?_, ?_⟩
    · change e 0 ∈ J.val
      simpa using J.property.2.1
    · intro a ha b hb
      change e (a + b) ∈ J.val
      rw [map_add]
      exact J.property.2.2.1 _ ha _ hb
    · intro c a ha
      change e (c • a) ∈ J.val
      rw [map_smul]
      exact J.property.2.2.2.1 c _ ha
    · intro a b hb
      change e (a * b) ∈ J.val ∧ e (b * a) ∈ J.val
      rw [hmul, hmul]
      exact J.property.2.2.2.2 (e a) (e b) hb⟩
  left_inv I := Subtype.ext (Set.preimage_image_eq I.val e.injective)
  right_inv J := Subtype.ext (Set.image_preimage_eq J.val e.surjective)
  map_rel_iff' := by
    intro I J
    exact Set.image_subset_image_iff e.injective

def maximalClosedIdealLinearEquiv (e : A ≃L[𝕜] B)
    (hmul : ∀ a b, e (a * b) = e a * e b) :
    MaximalClosedIdeals 𝕜 A ≃ MaximalClosedIdeals 𝕜 B :=
  maximalClosedIdealEquivCoatom.trans
    (((closedIdealLinearEquivOrderIso e hmul).toEquiv.subtypeEquiv
      (fun I => ((closedIdealLinearEquivOrderIso e hmul).isCoatom_iff I).symm)).trans
        maximalClosedIdealEquivCoatom.symm)

end Posets
