import Sigma.ComplexFinalFamilies
import Sigma.ComplexPairedFunctionalCharge

/-! The actual final ComplexJL product has coefficients in the construction's fixed
index set. The indexed charges used in the recursion represent its functionals
on the full generated test algebras. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup

abbrev ComplexFinalJLProduct (D : ComplexEnumeratedConstruction) := ComplexJL (D.family false) × ComplexJL (D.family true)

def ComplexEnumeratedConstruction.coefficients (D : ComplexEnumeratedConstruction)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) : lp (fun _ : FullAtom => ℂ) 1 :=
  complexPairedJLCoefficients (D.family_almostDisjoint false) (D.family_almostDisjoint true)
    (D.family_infinite false) (D.family_infinite true) (D.familyEquiv false) (D.familyEquiv true) φ

@[simp] theorem ComplexEnumeratedConstruction.coefficients_norm (D : ComplexEnumeratedConstruction)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) : ‖D.coefficients φ‖ = ‖φ‖ :=
  complexPairedJLCoefficients_norm _ _ _ _ _ _ _

theorem ComplexEnumeratedConstruction.atomCharge_agreement (D : ComplexEnumeratedConstruction) (p : FullAtom) :
    indexedAtomCharge D.infinityUltrafilter (complexFinalFamilyCharge D.data) p =
      pairedAtomCharge (D.family_almostDisjoint false) (D.family_almostDisjoint true)
        (D.familyEquiv false) (D.familyEquiv true) D.infinityUltrafilter p := by
  rcases p with ⟨side,q | (⟨i,bit⟩ | u)⟩
  · cases side <;> rfl
  · cases side <;> cases bit <;> rfl
  · cases side <;> rfl

def ComplexEnumeratedConstruction.functionalCharge (D : ComplexEnumeratedConstruction)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) : ComplexPairedMeasure :=
  complexIndexedCodeCharge D.infinityUltrafilter (complexFinalFamilyCharge D.data) (D.coefficients φ)
    (by simpa using hφ)

theorem ComplexEnumeratedConstruction.functionalCharge_eq (D : ComplexEnumeratedConstruction)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) :
    D.functionalCharge φ hφ =
      complexPairedFunctionalCharge (D.family_almostDisjoint false) (D.family_almostDisjoint true)
        (D.family_infinite false) (D.family_infinite true) (D.familyEquiv false) (D.familyEquiv true)
        D.infinityUltrafilter φ hφ := by
  apply ComplexUnitCharge.ext
  funext A
  apply tsum_congr
  intro p
  change D.coefficients φ p * (indexedAtomCharge D.infinityUltrafilter
    (complexFinalFamilyCharge D.data) p A : ℂ) = D.coefficients φ p *
      (pairedAtomCharge (D.family_almostDisjoint false) (D.family_almostDisjoint true)
        (D.familyEquiv false) (D.familyEquiv true) D.infinityUltrafilter p A : ℂ)
  rw [D.atomCharge_agreement p]

theorem ComplexEnumeratedConstruction.functionalCharge_generated (D : ComplexEnumeratedConstruction)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1)
    {A T : Set Point} (hA : A ∈ generatedAlgebra (D.family false))
    (hT : T ∈ generatedAlgebra (D.family true)) :
    ∃ (hmemA : complexCharacteristic A ∈ ComplexJL (D.family false)) (hmemT : complexCharacteristic T ∈ ComplexJL (D.family true)),
      D.functionalCharge φ hφ (pairedBaseSet A T) = φ (⟨complexCharacteristic A,hmemA⟩,⟨complexCharacteristic T,hmemT⟩) := by
  rw [D.functionalCharge_eq]
  exact complexPairedFunctionalCharge_generated _ _ _ _ _ _ _ D.infinityUltrafilter_free
    (D.infinityUltrafilter_avoids false) (D.infinityUltrafilter_avoids true) φ hφ hA hT

theorem ComplexEnumeratedConstruction.left_charge_agreement (D : ComplexEnumeratedConstruction)
    (a : ConstructionIndex) (φ : ℕ → ComplexFinalJLProduct D →L[ℂ] ℂ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hcode : D.leftCode a = fun n => D.coefficients (φ n)) (n : ℕ) :
    (D.data a).measures.1 n = D.functionalCharge (φ n) (hφ n) := by
  have h := congrArg (fun q : ComplexChargeSequences => q.1 n) (D.charge_agreement a)
  refine h.trans ?_
  apply ComplexUnitCharge.ext
  funext A
  change (∑' p, D.leftCode a n p * (indexedAtomCharge D.infinityUltrafilter (complexFinalFamilyCharge D.data) p A : ℂ)) = _
  rw [hcode]
  rfl

theorem ComplexEnumeratedConstruction.right_charge_agreement (D : ComplexEnumeratedConstruction)
    (a : ConstructionIndex) (φ : ℕ → ComplexFinalJLProduct D →L[ℂ] ℂ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hcode : D.rightCode a = fun n => D.coefficients (φ n)) (n : ℕ) :
    (D.data a).measures.2 n = D.functionalCharge (φ n) (hφ n) := by
  have h := congrArg (fun q : ComplexChargeSequences => q.2 n) (D.charge_agreement a)
  refine h.trans ?_
  apply ComplexUnitCharge.ext
  funext A
  change (∑' p, D.rightCode a n p * (indexedAtomCharge D.infinityUltrafilter (complexFinalFamilyCharge D.data) p A : ℂ)) = _
  rw [hcode]
  rfl

end SigmaNonprimarity


