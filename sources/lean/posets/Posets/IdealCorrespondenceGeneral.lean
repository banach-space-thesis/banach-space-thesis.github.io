import Posets.QuotientAlgebraEquiv
import Mathlib.Analysis.Normed.Operator.Banach

/-! Closed two-sided ideals under a surjective bounded algebra homomorphism.
The image is closed by the Banach open mapping theorem. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 A B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Mul B]
variable (Φ : BoundedHom 𝕜 A B)

def ClosedIdealsAboveKernel :=
  {I : Set A // IsClosedIdeal 𝕜 I ∧ {a | Φ a = 0} ⊆ I}

instance : PartialOrder (ClosedIdealsAboveKernel Φ) :=
  inferInstanceAs (PartialOrder (Subtype _))

theorem closedIdeal_preimage {J : Set B} (hJ : IsClosedIdeal 𝕜 J) :
    IsClosedIdeal 𝕜 (Φ ⁻¹' J) := by
  rcases hJ with ⟨hc, h0, ha, hs, hm⟩
  refine ⟨hc.preimage Φ.continuous, ?_, ?_, ?_, ?_⟩
  · change Φ 0 ∈ J
    simpa only [map_zero] using h0
  · intro a ha' b hb'
    change Φ (a + b) ∈ J
    rw [map_add]
    exact ha _ ha' _ hb'
  · intro c a ha'
    change Φ (c • a) ∈ J
    rw [map_smul]
    exact hs _ _ ha'
  · intro a b hb
    change Φ (a * b) ∈ J ∧ Φ (b * a) ∈ J
    rw [Φ.map_mul', Φ.map_mul']
    exact hm _ _ hb

theorem closedIdeal_preimage_image {I : Set A} (hI : IsClosedIdeal 𝕜 I)
    (hker : {a | Φ a = 0} ⊆ I) : Φ ⁻¹' (Φ '' I) = I := by
  ext a
  constructor
  · rintro ⟨b, hb, heq⟩
    have hd : a - b ∈ I := hker (by
      change Φ (a - b) = 0
      rw [map_sub, heq, sub_self])
    simpa only [add_sub_cancel] using hI.2.2.1 b hb (a - b) hd
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem closedIdeal_kernel_subset_preimage {J : Set B} (hJ : IsClosedIdeal 𝕜 J) :
    {a | Φ a = 0} ⊆ Φ ⁻¹' J := by
  intro a ha
  change Φ a ∈ J
  rw [ha]
  exact hJ.2.1

variable [CompleteSpace A] [CompleteSpace B]

theorem closedIdeal_image (hsurj : Function.Surjective Φ)
    {I : Set A} (hI : IsClosedIdeal 𝕜 I) (hker : {a | Φ a = 0} ⊆ I) :
    IsClosedIdeal 𝕜 (Φ '' I) := by
  have hc : IsClosed (Φ '' I) :=
    (Φ.toContinuousLinearMap.isQuotientMap hsurj).isClosed_preimage.mp (by
      rw [closedIdeal_preimage_image Φ hI hker]
      exact hI.1)
  refine ⟨hc, ⟨0, hI.2.1, map_zero Φ.toContinuousLinearMap⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, hI.2.2.1 _ ha _ hb, map_add Φ.toContinuousLinearMap a b⟩
  · rintro c _ ⟨a, ha, rfl⟩
    exact ⟨c • a, hI.2.2.2.1 c a ha, map_smul Φ.toContinuousLinearMap c a⟩
  · rintro a _ ⟨b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := hsurj a
    exact ⟨⟨a * b, (hI.2.2.2.2 a b hb).1, Φ.map_mul' a b⟩,
      ⟨b * a, (hI.2.2.2.2 a b hb).2, Φ.map_mul' b a⟩⟩

/-- Quotient ideals correspond to closed ideals containing the kernel.
The forward map is exactly inverse image. -/
def closedIdealQuotientOrderIso (hsurj : Function.Surjective Φ) :
    ClosedIdeal 𝕜 B ≃o ClosedIdealsAboveKernel Φ where
  toFun J := ⟨Φ ⁻¹' J.val, closedIdeal_preimage Φ J.property,
    closedIdeal_kernel_subset_preimage Φ J.property⟩
  invFun I := ⟨Φ '' I.val, closedIdeal_image Φ hsurj I.property.1 I.property.2⟩
  left_inv J := Subtype.ext (image_preimage_eq _ hsurj)
  right_inv I := Subtype.ext (closedIdeal_preimage_image Φ I.property.1 I.property.2)
  map_rel_iff' := by
    intro I J
    change Φ ⁻¹' I.val ⊆ Φ ⁻¹' J.val ↔ I.val ⊆ J.val
    constructor
    · intro h b hb
      obtain ⟨a, rfl⟩ := hsurj b
      exact h hb
    · exact preimage_mono

end Posets
