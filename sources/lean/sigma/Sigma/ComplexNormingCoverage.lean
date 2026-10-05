import Sigma.ComplexCrossedCoefficients

/-! Every actual norming sequence on either final crossed summand occurs in
the construction after selection, with the stored charges agreeing with its
projected evaluations on the entire pair of generated Boolean algebras. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

def ComplexEnumeratedConstruction.codeAtSide (D : ComplexEnumeratedConstruction) (side : Bool) :
    ConstructionIndex → ComplexFullCoefficientRows := if side then D.rightCode else D.leftCode

def ComplexEnumeratedConstruction.chargeAtSide (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) : ℕ → ComplexPairedMeasure :=
  if side then (D.data a).measures.2 else (D.data a).measures.1

theorem ComplexEnumeratedConstruction.codeAtSide_covers (D : ComplexEnumeratedConstruction) (side : Bool)
    (c : ComplexFullCoefficientRows) (hc : ComplexFullCodeAdmissible side c) :
    ∃ a, D.codeAtSide side a = c := by
  cases side
  · exact D.left_covers c hc
  · exact D.right_covers c hc

theorem ComplexEnumeratedConstruction.chargeAtSide_agreement (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (φ : ℕ → ComplexFinalJLProduct D →L[ℂ] ℂ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (φ n)) (n : ℕ) :
    D.chargeAtSide side a n = D.functionalCharge (φ n) (hφ n) := by
  cases side
  · exact D.left_charge_agreement a φ hφ hcode n
  · exact D.right_charge_agreement a φ hφ hcode n

theorem ComplexEnumeratedConstruction.norming_sequence_covered (D : ComplexEnumeratedConstruction) (side : Bool)
    (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ) (he : IsComplexNorming e) :
    ∃ (k : ℕ → ℕ) (a : ConstructionIndex), D.codeAtSide side a =
      fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))) := by
  obtain ⟨k,hk⟩ := D.normingRows_admissible side e he
  obtain ⟨a,ha⟩ := D.codeAtSide_covers side _ hk
  exact ⟨k,a,ha⟩

theorem ComplexEnumeratedConstruction.norming_sequence_charge_covered (D : ComplexEnumeratedConstruction) (side : Bool)
    (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ) (he : IsComplexNorming e) :
    ∃ (k : ℕ → ℕ) (a : ConstructionIndex),
      (D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n)))) ∧
      ∀ (n : ℕ) {A T : Set Point}, A ∈ generatedAlgebra (D.family false) →
        T ∈ generatedAlgebra (D.family true) →
        ∃ (hA : complexCharacteristic A ∈ ComplexJL (D.family false)) (hT : complexCharacteristic T ∈ ComplexJL (D.family true)),
          D.chargeAtSide side a n (pairedBaseSet A T) =
            e (k n) (D.crossedProjection side (⟨complexCharacteristic A,hA⟩,⟨complexCharacteristic T,hT⟩)) := by
  obtain ⟨k,a,ha⟩ := D.norming_sequence_covered side e he
  obtain ⟨c,hc⟩ := he
  have hunit (n : ℕ) : ‖D.extendCrossedFunctional side (e (k n))‖ ≤ 1 :=
    (D.extendCrossedFunctional_norm_le side _).trans (hc.2.2.1 (k n))
  refine ⟨k,a,ha,?_⟩
  intro n A T hA hT
  rw [D.chargeAtSide_agreement side a (fun n => D.extendCrossedFunctional side (e (k n))) hunit ha n]
  exact D.functionalCharge_generated _ (hunit n) hA hT

end SigmaNonprimarity


