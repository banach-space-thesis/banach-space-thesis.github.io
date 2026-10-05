import Sigma.IndexedFamily
import Sigma.FunctionalCharge
import ThesisCommon.Analysis.LpOneReindex

/-! Explicit coordinates for every compactum atom, including infinity, and
the transported isometric representation of the actual JL dual. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace
attribute [local instance] jlDualGroup jlDualSpace

abbrev IndexedAtom (Λ : Type) := Point ⊕ (Λ ⊕ Unit)

def compactumAtomEquiv {Λ : Type} {B : Set (Set Point)} (e : Λ ≃ B) :
    IndexedAtom Λ ≃ AUCompactum B where
  toFun
    | .inl p => ↑(Sum.inl p : MrowkaBase B)
    | .inr (.inl i) => ↑(Sum.inr (e i) : MrowkaBase B)
    | .inr (.inr _) => OnePoint.infty
  invFun := OnePoint.rec (Sum.inr (Sum.inr ()))
    (fun q => match q with
      | .inl p => .inl p
      | .inr b => .inr (.inl (e.symm b)))
  left_inv := by
    rintro (p | (i | u))
    · rfl
    · change Sum.inr (Sum.inl (e.symm (e i))) = Sum.inr (Sum.inl i)
      rw [e.symm_apply_apply]
    · cases u; rfl
  right_inv := by
    intro p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe q => cases q with
      | inl p => rfl
      | inr b =>
        change (↑(Sum.inr (e (e.symm b)) : MrowkaBase B) : AUCompactum B) = ↑(Sum.inr b : MrowkaBase B)
        rw [e.apply_symm_apply]

@[simp] theorem compactumAtomEquiv_base {Λ : Type} {B : Set (Set Point)}
    (e : Λ ≃ B) (p : Point) : compactumAtomEquiv e (.inl p) = ↑(Sum.inl p : MrowkaBase B) := rfl

@[simp] theorem compactumAtomEquiv_family {Λ : Type} {B : Set (Set Point)}
    (e : Λ ≃ B) (i : Λ) : compactumAtomEquiv e (.inr (.inl i)) = ↑(Sum.inr (e i) : MrowkaBase B) := rfl

@[simp] theorem compactumAtomEquiv_infty {Λ : Type} {B : Set (Set Point)}
    (e : Λ ≃ B) : compactumAtomEquiv e (.inr (.inr ())) = OnePoint.infty := rfl

def indexedJLDualEquiv {Λ : Type} {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (e : Λ ≃ B) : (JL B →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : IndexedAtom Λ => ℝ) 1 :=
  (jlDualEquiv hB hInf).trans (lpOneReindex (compactumAtomEquiv e))

@[simp] theorem indexedJLDualEquiv_apply {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : JL B →L[ℝ] ℝ)
    (p : IndexedAtom Λ) :
    indexedJLDualEquiv hB hInf e φ p = jlDualEquiv hB hInf φ (compactumAtomEquiv e p) := rfl

theorem indexedJLDual_apply_hasSum {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : JL B →L[ℝ] ℝ) (f : JL B) :
    HasSum (fun p => indexedJLDualEquiv hB hInf e φ p *
      jlContinuousEquiv hB hInf f (compactumAtomEquiv e p)) (φ f) := by
  simp only [indexedJLDualEquiv_apply]
  exact ((compactumAtomEquiv e).hasSum_iff
    (f := fun p : AUCompactum B => jlDualEquiv hB hInf φ p * jlContinuousEquiv hB hInf f p)).mpr
    (jlDual_apply_hasSum hB hInf φ f)

end SigmaNonprimarity
