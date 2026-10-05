import Sigma.ComplexFlipEvaluations
import Sigma.ComplexIndexedAtoms

/-! The coordinate action on the actual ComplexJL dual follows from uniqueness of
the atomic representation. Antisymmetric functionals have opposite paired
coefficients and zero infinity coefficient. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace

theorem complexIndexedJLDual_eq_of_hasSum {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : ComplexJL B →L[ℂ] ℂ)
    (c : lp (fun _ : IndexedAtom Λ => ℂ) 1)
    (h : ∀ f : ComplexJL B, HasSum (fun p => c p * complexJLContinuousEquiv hB hInf f (compactumAtomEquiv e p)) (φ f)) :
    complexIndexedJLDualEquiv hB hInf e φ = c := by
  let ψ := (complexIndexedJLDualEquiv hB hInf e).symm c
  have hc : complexIndexedJLDualEquiv hB hInf e ψ = c := LinearIsometryEquiv.apply_symm_apply _ _
  have heq : ψ = φ := by
    apply ContinuousLinearMap.ext
    intro f
    have hs := complexIndexedJLDual_apply_hasSum hB hInf e ψ f
    rw [hc] at hs
    exact hs.unique (h f)
  rw [← heq]
  exact hc

theorem ComplexEnumeratedConstruction.indexedDual_flip (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexJL (D.family side) →L[ℂ] ℂ) :
    complexIndexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side)
      (φ.comp (D.flipJL side)) =
    complexLpOneReindex indexedAtomFlip
      (complexIndexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ) := by
  apply complexIndexedJLDual_eq_of_hasSum
  intro f
  let c := complexIndexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ
  let v := fun p => complexJLContinuousEquiv (D.family_almostDisjoint side) (D.family_infinite side) f
    (compactumAtomEquiv (D.familyEquiv side) p)
  have hs : HasSum (fun p => c p * v (indexedAtomFlip p)) (φ (D.flipJL side f)) := by
    have h := complexIndexedJLDual_apply_hasSum (D.family_almostDisjoint side) (D.family_infinite side)
      (D.familyEquiv side) φ (D.flipJL side f)
    simpa only [D.complexJLContinuous_flip] using h
  have ht := indexedAtomFlip.hasSum_iff (f := fun p => c p * v (indexedAtomFlip p)) |>.mpr hs
  have hi (p : IndexedAtom (ConstructionIndex × Bool)) : indexedAtomFlip (indexedAtomFlip p) = p :=
    indexedAtomFlip_involutive p
  simpa only [Function.comp_def,hi,complexLpOneReindex_apply] using ht

theorem ComplexEnumeratedConstruction.indexedDual_antisymmetric (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexJL (D.family side) →L[ℂ] ℂ) (hφ : φ.comp (D.flipJL side) = -φ)
    (p : IndexedAtom (ConstructionIndex × Bool)) :
    complexIndexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ
      (indexedAtomFlip p) =
    -complexIndexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ p := by
  have h := D.indexedDual_flip side φ
  rw [hφ,map_neg] at h
  exact (congrArg (fun c : lp (fun _ : IndexedAtom (ConstructionIndex × Bool) => ℂ) 1 => c p) h).symm

theorem ComplexEnumeratedConstruction.indexedDual_infinity_zero (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexJL (D.family side) →L[ℂ] ℂ) (hφ : φ.comp (D.flipJL side) = -φ) :
    complexIndexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ
      (.inr (.inr ())) = 0 := by
  have h := D.indexedDual_antisymmetric side φ hφ (.inr (.inr ()))
  have hi : indexedAtomFlip (.inr (.inr ())) = .inr (.inr ()) := rfl
  rw [hi] at h
  linear_combination (1/2 : ℂ) * h

end SigmaNonprimarity


