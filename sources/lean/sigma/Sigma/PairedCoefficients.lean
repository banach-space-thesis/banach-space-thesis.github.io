import Sigma.IndexedAtoms
import ThesisCommon.Analysis.LpOnePair
import ThesisCommon.Analysis.ProductDualNorm

/-! Full coefficients of an actual functional on the product of two JL
spaces. Their combined ell-one norm is exactly the functional norm. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace

local instance pairedJLGroup (B Bt : Set (Set Point)) : NormedAddCommGroup (JL B × JL Bt) := inferInstance
local instance pairedJLSpace (B Bt : Set (Set Point)) : NormedSpace ℝ (JL B × JL Bt) := inferInstance
local instance pairedJLDualGroup (B Bt : Set (Set Point)) : NormedAddCommGroup ((JL B × JL Bt) →L[ℝ] ℝ) := inferInstance

def pairedJLCoefficients {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (JL B × JL Bt) →L[ℝ] ℝ) :
    lp (fun _ : Bool × IndexedAtom Λ => ℝ) 1 :=
  lpOnePair (indexedJLDualEquiv hB hInf e (dualProdLeft φ))
    (indexedJLDualEquiv hBt htInf et (dualProdRight φ))

@[simp] theorem pairedJLCoefficients_false {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (JL B × JL Bt) →L[ℝ] ℝ) (p : IndexedAtom Λ) :
    pairedJLCoefficients hB hBt hInf htInf e et φ (false,p) =
      indexedJLDualEquiv hB hInf e (dualProdLeft φ) p := rfl

@[simp] theorem pairedJLCoefficients_true {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (JL B × JL Bt) →L[ℝ] ℝ) (p : IndexedAtom Λ) :
    pairedJLCoefficients hB hBt hInf htInf e et φ (true,p) =
      indexedJLDualEquiv hBt htInf et (dualProdRight φ) p := rfl

@[simp] theorem pairedJLCoefficients_norm {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (JL B × JL Bt) →L[ℝ] ℝ) :
    ‖pairedJLCoefficients hB hBt hInf htInf e et φ‖ = ‖φ‖ := by
  rw [pairedJLCoefficients,lpOnePair_norm,LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map,
    ← dualProd_norm]

def indexedPairValue {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (f : JL B) (g : JL Bt) (p : Bool × IndexedAtom Λ) : ℝ :=
  if p.1 then jlContinuousEquiv hBt htInf g (compactumAtomEquiv et p.2)
  else jlContinuousEquiv hB hInf f (compactumAtomEquiv e p.2)

theorem pairedJLCoefficients_apply_hasSum {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (φ : (JL B × JL Bt) →L[ℝ] ℝ) (f : JL B) (g : JL Bt) :
    HasSum (fun p => pairedJLCoefficients hB hBt hInf htInf e et φ p *
      indexedPairValue hB hBt hInf htInf e et f g p) (φ (f,g)) := by
  let L : IndexedAtom Λ → ℝ := fun p => indexedJLDualEquiv hB hInf e (dualProdLeft φ) p *
    jlContinuousEquiv hB hInf f (compactumAtomEquiv e p)
  let R : IndexedAtom Λ → ℝ := fun p => indexedJLDualEquiv hBt htInf et (dualProdRight φ) p *
    jlContinuousEquiv hBt htInf g (compactumAtomEquiv et p)
  have hs : HasSum (Sum.elim L R) (dualProdLeft φ f + dualProdRight φ g) :=
    HasSum.sum (f := Sum.elim L R) (indexedJLDual_apply_hasSum hB hInf e (dualProdLeft φ) f)
      (indexedJLDual_apply_hasSum hBt htInf et (dualProdRight φ) g)
  have hp := (Equiv.boolProdEquivSum (IndexedAtom Λ)).hasSum_iff (f := Sum.elim L R) |>.mpr hs
  rw [dualProd_apply φ f g]
  convert hp using 1
  funext ⟨side,p⟩
  cases side <;> rfl

end SigmaNonprimarity
