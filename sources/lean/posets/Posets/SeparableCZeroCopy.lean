import Posets.CountableSupportCoordinates
import Posets.FamilySupport
import PosetsCommon.CZeroHomeomorph
import PosetsCommon.CountableCZeroProduct

noncomputable section
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

/-- Restriction of a bounded isomorphism to the inverse image of a subspace. -/
def submoduleComapEquiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : E ≃L[𝕜] F) (W : Submodule 𝕜 F) :
    W.comap e.toLinearMap ≃L[𝕜] W := by
  let f := (e.toContinuousLinearMap.comp (W.comap e.toLinearMap).subtypeL).codRestrict W
    (fun x => x.property)
  let g := (e.symm.toContinuousLinearMap.comp W.subtypeL).codRestrict
    (W.comap e.toLinearMap) (fun y => by
      change e (e.symm y.val) ∈ W
      simpa only [e.apply_symm_apply] using y.property)
  exact ContinuousLinearEquiv.equivOfInverse f g
    (fun x => Subtype.ext (e.symm_apply_apply x.val))
    (fun y => Subtype.ext (e.apply_symm_apply y.val))

/-- Lemma 4.4. Countable support is split by disjoint tails, and its two
discrete coordinate sets are numbered together to obtain a closed copy of c₀. -/
theorem lemma_4_4_proof (𝕜 : Type) [RCLike 𝕜] (𝒜 : Set (Set ℕ)) : Lemma_4_4 𝕜 𝒜 := by
  intro h𝒜 X hX
  letI := hX
  let S := familySupportSet 𝕜 (X : Set (Space 𝕜 𝒜))
  have hS : S.Countable := familySupportSet_countable_of_separable _
  letI : Countable S := hS.to_subtype
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  let e : Space 𝕜 𝒜 ≃L[𝕜] C₀(PUnit × Mrowka 𝒜, 𝕜) :=
    ThesisCommon.cZeroHomeomorphEquiv (Homeomorph.punitProd (Mrowka 𝒜))
  let W := JFA.mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := PUnit) S
  let Y := W.comap e.toLinearMap
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro f hf
    change ∀ d A, A ∉ S → e f (d, Sum.inr A) = 0
    intro d A hA
    change f (Sum.inr A) = 0
    by_contra hne
    exact hA ⟨f, hf, hne⟩
  · exact (JFA.mrowkaSupportedSubmodule_isClosed (𝕜 := 𝕜) (D := PUnit) S).preimage e.continuous
  · exact ⟨((submoduleComapEquiv e W).trans (countableSupportEquiv S h𝒜)).trans
      (ThesisCommon.countableCZeroProductEquiv (ι := PUnit × ℕ) (κ := PUnit × S))⟩

end Posets
