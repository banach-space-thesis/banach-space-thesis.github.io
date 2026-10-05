import Sigma.FlipEvaluations

/-! The coordinate action on the actual JL dual follows from uniqueness of
the atomic representation. Antisymmetric functionals have opposite paired
coefficients and zero infinity coefficient. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace

theorem indexedJLDual_eq_of_hasSum {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : JL B →L[ℝ] ℝ)
    (c : lp (fun _ : IndexedAtom Λ => ℝ) 1)
    (h : ∀ f : JL B, HasSum (fun p => c p * jlContinuousEquiv hB hInf f (compactumAtomEquiv e p)) (φ f)) :
    indexedJLDualEquiv hB hInf e φ = c := by
  let ψ := (indexedJLDualEquiv hB hInf e).symm c
  have hc : indexedJLDualEquiv hB hInf e ψ = c := LinearIsometryEquiv.apply_symm_apply _ _
  have heq : ψ = φ := by
    apply ContinuousLinearMap.ext
    intro f
    have hs := indexedJLDual_apply_hasSum hB hInf e ψ f
    rw [hc] at hs
    exact hs.unique (h f)
  rw [← heq]
  exact hc

theorem EnumeratedConstruction.indexedDual_flip (D : EnumeratedConstruction) (side : Bool)
    (φ : JL (D.family side) →L[ℝ] ℝ) :
    indexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side)
      (φ.comp (D.flipJL side)) =
    lpOneReindex indexedAtomFlip
      (indexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ) := by
  apply indexedJLDual_eq_of_hasSum
  intro f
  let c := indexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ
  let v := fun p => jlContinuousEquiv (D.family_almostDisjoint side) (D.family_infinite side) f
    (compactumAtomEquiv (D.familyEquiv side) p)
  have hs : HasSum (fun p => c p * v (indexedAtomFlip p)) (φ (D.flipJL side f)) := by
    have h := indexedJLDual_apply_hasSum (D.family_almostDisjoint side) (D.family_infinite side)
      (D.familyEquiv side) φ (D.flipJL side f)
    simpa only [D.jlContinuous_flip] using h
  have ht := indexedAtomFlip.hasSum_iff (f := fun p => c p * v (indexedAtomFlip p)) |>.mpr hs
  have hi (p : IndexedAtom (ConstructionIndex × Bool)) : indexedAtomFlip (indexedAtomFlip p) = p :=
    indexedAtomFlip_involutive p
  simpa only [Function.comp_def,hi,lpOneReindex_apply] using ht

theorem EnumeratedConstruction.indexedDual_antisymmetric (D : EnumeratedConstruction) (side : Bool)
    (φ : JL (D.family side) →L[ℝ] ℝ) (hφ : φ.comp (D.flipJL side) = -φ)
    (p : IndexedAtom (ConstructionIndex × Bool)) :
    indexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ
      (indexedAtomFlip p) =
    -indexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ p := by
  have h := D.indexedDual_flip side φ
  rw [hφ,map_neg] at h
  exact (congrArg (fun c : lp (fun _ : IndexedAtom (ConstructionIndex × Bool) => ℝ) 1 => c p) h).symm

theorem EnumeratedConstruction.indexedDual_infinity_zero (D : EnumeratedConstruction) (side : Bool)
    (φ : JL (D.family side) →L[ℝ] ℝ) (hφ : φ.comp (D.flipJL side) = -φ) :
    indexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) φ
      (.inr (.inr ())) = 0 := by
  have h := D.indexedDual_antisymmetric side φ hφ (.inr (.inr ()))
  have hi : indexedAtomFlip (.inr (.inr ())) = .inr (.inr ()) := rfl
  rw [hi] at h
  linarith

end SigmaNonprimarity
