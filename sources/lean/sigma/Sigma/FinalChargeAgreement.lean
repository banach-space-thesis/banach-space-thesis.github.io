import Sigma.FinalFamilies
import Sigma.PairedFunctionalCharge

/-! The actual final JL product has coefficients in the construction's fixed
index set. The indexed charges used in the recursion represent its functionals
on the full generated test algebras. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup

abbrev FinalJLProduct (D : EnumeratedConstruction) := JL (D.family false) × JL (D.family true)

def EnumeratedConstruction.coefficients (D : EnumeratedConstruction)
    (φ : FinalJLProduct D →L[ℝ] ℝ) : lp (fun _ : FullAtom => ℝ) 1 :=
  pairedJLCoefficients (D.family_almostDisjoint false) (D.family_almostDisjoint true)
    (D.family_infinite false) (D.family_infinite true) (D.familyEquiv false) (D.familyEquiv true) φ

@[simp] theorem EnumeratedConstruction.coefficients_norm (D : EnumeratedConstruction)
    (φ : FinalJLProduct D →L[ℝ] ℝ) : ‖D.coefficients φ‖ = ‖φ‖ :=
  pairedJLCoefficients_norm _ _ _ _ _ _ _

theorem EnumeratedConstruction.atomCharge_agreement (D : EnumeratedConstruction) (p : FullAtom) :
    indexedAtomCharge D.infinityUltrafilter (finalFamilyCharge D.data) p =
      pairedAtomCharge (D.family_almostDisjoint false) (D.family_almostDisjoint true)
        (D.familyEquiv false) (D.familyEquiv true) D.infinityUltrafilter p := by
  rcases p with ⟨side,q | (⟨i,bit⟩ | u)⟩
  · cases side <;> rfl
  · cases side <;> cases bit <;> rfl
  · cases side <;> rfl

def EnumeratedConstruction.functionalCharge (D : EnumeratedConstruction)
    (φ : FinalJLProduct D →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) : PairedMeasure :=
  indexedCodeCharge D.infinityUltrafilter (finalFamilyCharge D.data) (D.coefficients φ)
    (by simpa using hφ)

theorem EnumeratedConstruction.functionalCharge_eq (D : EnumeratedConstruction)
    (φ : FinalJLProduct D →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) :
    D.functionalCharge φ hφ =
      pairedFunctionalCharge (D.family_almostDisjoint false) (D.family_almostDisjoint true)
        (D.family_infinite false) (D.family_infinite true) (D.familyEquiv false) (D.familyEquiv true)
        D.infinityUltrafilter φ hφ := by
  apply UnitCharge.ext
  funext A
  apply tsum_congr
  intro p
  rw [D.atomCharge_agreement p]
  rfl

theorem EnumeratedConstruction.functionalCharge_generated (D : EnumeratedConstruction)
    (φ : FinalJLProduct D →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    {A T : Set Point} (hA : A ∈ generatedAlgebra (D.family false))
    (hT : T ∈ generatedAlgebra (D.family true)) :
    ∃ (hmemA : characteristic A ∈ JL (D.family false)) (hmemT : characteristic T ∈ JL (D.family true)),
      D.functionalCharge φ hφ (pairedBaseSet A T) = φ (⟨characteristic A,hmemA⟩,⟨characteristic T,hmemT⟩) := by
  rw [D.functionalCharge_eq]
  exact pairedFunctionalCharge_generated _ _ _ _ _ _ _ D.infinityUltrafilter_free
    (D.infinityUltrafilter_avoids false) (D.infinityUltrafilter_avoids true) φ hφ hA hT

theorem EnumeratedConstruction.left_charge_agreement (D : EnumeratedConstruction)
    (a : ConstructionIndex) (φ : ℕ → FinalJLProduct D →L[ℝ] ℝ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hcode : D.leftCode a = fun n => D.coefficients (φ n)) (n : ℕ) :
    (D.data a).measures.1 n = D.functionalCharge (φ n) (hφ n) := by
  have h := congrArg (fun q : ChargeSequences => q.1 n) (D.charge_agreement a)
  refine h.trans ?_
  apply UnitCharge.ext
  funext A
  change (∑' p, D.leftCode a n p * indexedAtomCharge D.infinityUltrafilter (finalFamilyCharge D.data) p A) = _
  rw [hcode]
  rfl

theorem EnumeratedConstruction.right_charge_agreement (D : EnumeratedConstruction)
    (a : ConstructionIndex) (φ : ℕ → FinalJLProduct D →L[ℝ] ℝ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hcode : D.rightCode a = fun n => D.coefficients (φ n)) (n : ℕ) :
    (D.data a).measures.2 n = D.functionalCharge (φ n) (hφ n) := by
  have h := congrArg (fun q : ChargeSequences => q.2 n) (D.charge_agreement a)
  refine h.trans ?_
  apply UnitCharge.ext
  funext A
  change (∑' p, D.rightCode a n p * indexedAtomCharge D.infinityUltrafilter (finalFamilyCharge D.data) p A) = _
  rw [hcode]
  rfl

end SigmaNonprimarity
