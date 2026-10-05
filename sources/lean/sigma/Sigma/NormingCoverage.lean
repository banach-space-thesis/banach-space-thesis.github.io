import Sigma.CrossedCoefficients

/-! Every actual norming sequence on either final crossed summand occurs in
the construction after selection, with the stored charges agreeing with its
projected evaluations on the entire pair of generated Boolean algebras. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

def EnumeratedConstruction.codeAtSide (D : EnumeratedConstruction) (side : Bool) :
    ConstructionIndex → FullCoefficientRows := if side then D.rightCode else D.leftCode

def EnumeratedConstruction.chargeAtSide (D : EnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) : ℕ → PairedMeasure :=
  if side then (D.data a).measures.2 else (D.data a).measures.1

theorem EnumeratedConstruction.codeAtSide_covers (D : EnumeratedConstruction) (side : Bool)
    (c : FullCoefficientRows) (hc : FullCodeAdmissible side c) :
    ∃ a, D.codeAtSide side a = c := by
  cases side
  · exact D.left_covers c hc
  · exact D.right_covers c hc

theorem EnumeratedConstruction.chargeAtSide_agreement (D : EnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (φ : ℕ → FinalJLProduct D →L[ℝ] ℝ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (φ n)) (n : ℕ) :
    D.chargeAtSide side a n = D.functionalCharge (φ n) (hφ n) := by
  cases side
  · exact D.left_charge_agreement a φ hφ hcode n
  · exact D.right_charge_agreement a φ hφ hcode n

theorem EnumeratedConstruction.norming_sequence_covered (D : EnumeratedConstruction) (side : Bool)
    (e : ℕ → FinalCandidate D side →L[ℝ] ℝ) (he : IsNorming e) :
    ∃ (k : ℕ → ℕ) (a : ConstructionIndex), D.codeAtSide side a =
      fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))) := by
  obtain ⟨k,hk⟩ := D.normingRows_admissible side e he
  obtain ⟨a,ha⟩ := D.codeAtSide_covers side _ hk
  exact ⟨k,a,ha⟩

theorem EnumeratedConstruction.norming_sequence_charge_covered (D : EnumeratedConstruction) (side : Bool)
    (e : ℕ → FinalCandidate D side →L[ℝ] ℝ) (he : IsNorming e) :
    ∃ (k : ℕ → ℕ) (a : ConstructionIndex),
      (D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n)))) ∧
      ∀ (n : ℕ) {A T : Set Point}, A ∈ generatedAlgebra (D.family false) →
        T ∈ generatedAlgebra (D.family true) →
        ∃ (hA : characteristic A ∈ JL (D.family false)) (hT : characteristic T ∈ JL (D.family true)),
          D.chargeAtSide side a n (pairedBaseSet A T) =
            e (k n) (D.crossedProjection side (⟨characteristic A,hA⟩,⟨characteristic T,hT⟩)) := by
  obtain ⟨k,a,ha⟩ := D.norming_sequence_covered side e he
  obtain ⟨c,hc⟩ := he
  have hunit (n : ℕ) : ‖D.extendCrossedFunctional side (e (k n))‖ ≤ 1 :=
    (D.extendCrossedFunctional_norm_le side _).trans (hc.2.2.1 (k n))
  refine ⟨k,a,ha,?_⟩
  intro n A T hA hT
  rw [D.chargeAtSide_agreement side a (fun n => D.extendCrossedFunctional side (e (k n))) hunit ha n]
  exact D.functionalCharge_generated _ (hunit n) hA hT

end SigmaNonprimarity
