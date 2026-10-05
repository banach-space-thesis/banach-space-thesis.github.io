import Sigma.ComplexIndexedAtoms
import ThesisCommon.Analysis.SigmaComplexCoefficientOperators
import ThesisCommon.Analysis.SigmaComplexProductDualNorm

/-! Full coefficients of an actual functional on the product of two ComplexJL
spaces. Their combined ell-one norm is exactly the functional norm. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace

local instance complexPairedJLGroup (B Bt : Set (Set Point)) : NormedAddCommGroup (ComplexJL B × ComplexJL Bt) := inferInstance
local instance complexPairedJLSpace (B Bt : Set (Set Point)) : NormedSpace ℂ (ComplexJL B × ComplexJL Bt) := inferInstance
local instance complexPairedJLDualGroup (B Bt : Set (Set Point)) : NormedAddCommGroup ((ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) := inferInstance

def complexPairedJLCoefficients {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) :
    lp (fun _ : Bool × IndexedAtom Λ => ℂ) 1 :=
  complexLpOnePair (complexIndexedJLDualEquiv hB hInf e (complexDualProdLeft φ))
    (complexIndexedJLDualEquiv hBt htInf et (complexDualProdRight φ))

@[simp] theorem complexPairedJLCoefficients_false {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) (p : IndexedAtom Λ) :
    complexPairedJLCoefficients hB hBt hInf htInf e et φ (false,p) =
      complexIndexedJLDualEquiv hB hInf e (complexDualProdLeft φ) p := rfl

@[simp] theorem complexPairedJLCoefficients_true {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) (p : IndexedAtom Λ) :
    complexPairedJLCoefficients hB hBt hInf htInf e et φ (true,p) =
      complexIndexedJLDualEquiv hBt htInf et (complexDualProdRight φ) p := rfl

@[simp] theorem complexPairedJLCoefficients_norm {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) :
    ‖complexPairedJLCoefficients hB hBt hInf htInf e et φ‖ = ‖φ‖ := by
  rw [complexPairedJLCoefficients,complexLpOnePair_norm,LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map,
    ← complexDualProd_norm]

def complexIndexedPairValue {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (f : ComplexJL B) (g : ComplexJL Bt) (p : Bool × IndexedAtom Λ) : ℂ :=
  if p.1 then complexJLContinuousEquiv hBt htInf g (compactumAtomEquiv et p.2)
  else complexJLContinuousEquiv hB hInf f (compactumAtomEquiv e p.2)

theorem complexPairedJLCoefficients_apply_hasSum {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) (f : ComplexJL B) (g : ComplexJL Bt) :
    HasSum (fun p => complexPairedJLCoefficients hB hBt hInf htInf e et φ p *
      complexIndexedPairValue hB hBt hInf htInf e et f g p) (φ (f,g)) := by
  let L : IndexedAtom Λ → ℂ := fun p => complexIndexedJLDualEquiv hB hInf e (complexDualProdLeft φ) p *
    complexJLContinuousEquiv hB hInf f (compactumAtomEquiv e p)
  let R : IndexedAtom Λ → ℂ := fun p => complexIndexedJLDualEquiv hBt htInf et (complexDualProdRight φ) p *
    complexJLContinuousEquiv hBt htInf g (compactumAtomEquiv et p)
  have hs : HasSum (Sum.elim L R) (complexDualProdLeft φ f + complexDualProdRight φ g) :=
    HasSum.sum (f := Sum.elim L R) (complexIndexedJLDual_apply_hasSum hB hInf e (complexDualProdLeft φ) f)
      (complexIndexedJLDual_apply_hasSum hBt htInf et (complexDualProdRight φ) g)
  have hp := (Equiv.boolProdEquivSum (IndexedAtom Λ)).hasSum_iff (f := Sum.elim L R) |>.mpr hs
  rw [complexDualProd_apply φ f g]
  convert hp using 1
  funext ⟨side,p⟩
  cases side <;> rfl

end SigmaNonprimarity


