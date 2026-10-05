import Sigma.ComplexJLDual
import Sigma.IndexedAtoms
import ThesisCommon.Analysis.SigmaComplexCoefficientOperators

noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace

def complexIndexedJLDualEquiv {Λ : Type} {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (e : Λ ≃ B) : (ComplexJL B →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : IndexedAtom Λ => ℂ) 1 :=
  (complexJLDualEquiv hB hInf).trans (complexLpOneReindex (compactumAtomEquiv e))

@[simp] theorem complexIndexedJLDualEquiv_apply {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : ComplexJL B →L[ℂ] ℂ)
    (p : IndexedAtom Λ) :
    complexIndexedJLDualEquiv hB hInf e φ p = complexJLDualEquiv hB hInf φ (compactumAtomEquiv e p) := rfl

theorem complexIndexedJLDual_apply_hasSum {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : ComplexJL B →L[ℂ] ℂ) (f : ComplexJL B) :
    HasSum (fun p => complexIndexedJLDualEquiv hB hInf e φ p *
      complexJLContinuousEquiv hB hInf f (compactumAtomEquiv e p)) (φ f) := by
  simp only [complexIndexedJLDualEquiv_apply]
  exact ((compactumAtomEquiv e).hasSum_iff
    (f := fun p : AUCompactum B => complexJLDualEquiv hB hInf φ p * complexJLContinuousEquiv hB hInf f p)).mpr
    (complexJLDual_apply_hasSum hB hInf φ f)


end SigmaNonprimarity

