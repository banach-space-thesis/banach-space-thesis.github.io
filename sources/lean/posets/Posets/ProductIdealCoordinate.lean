import Posets.ProductIdealActive

/-! Every coordinate's closed ideal set embeds in the closed ideal set of
the bounded product, by inverse image under coordinate evaluation. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set ThesisCommon
open scoped ENNReal
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} (C : ι → Type*) [∀ i, NormedRing (C i)]
  [∀ i, NormedAlgebra 𝕜 (C i)]

def lpCoordinateIdeal (i : ι) (I : ClosedIdeal 𝕜 (C i)) : ClosedIdeal 𝕜 (lp C ∞) := by
  refine ⟨{x | x i ∈ I.val}, I.property.1.preimage
    ((continuous_apply i).comp lp.uniformContinuous_coe.continuous), I.property.2.1,
    ?_, ?_, ?_⟩
  · intro x hx y hy
    exact I.property.2.2.1 _ hx _ hy
  · intro c x hx
    exact I.property.2.2.2.1 c _ hx
  · intro x y hy
    exact I.property.2.2.2.2 (x i) (y i) hy

def coordinateClosedIdealEmbedding (i : ι) :
    ClosedIdeal 𝕜 (C i) ↪ ClosedIdeal 𝕜 (lp C ∞) where
  toFun := lpCoordinateIdeal C i
  inj' := by
    intro I J hIJ
    apply Subtype.ext
    ext a
    have hm := congrArg (fun K : ClosedIdeal 𝕜 (lp C ∞) => lp.single ∞ i a ∈ K.val) hIJ
    change (lp.single ∞ i a i ∈ I.val) = (lp.single ∞ i a i ∈ J.val) at hm
    simpa using iff_of_eq hm

theorem finite_coordinate_closedIdeals_of_finite_product
    [Finite (ClosedIdeal 𝕜 (lp C ∞))] (i : ι) : Finite (ClosedIdeal 𝕜 (C i)) :=
  Finite.of_injective (coordinateClosedIdealEmbedding (𝕜 := 𝕜) C i)
    (coordinateClosedIdealEmbedding (𝕜 := 𝕜) C i).injective

end Posets
