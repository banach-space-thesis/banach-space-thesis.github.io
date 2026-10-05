import Sigma.ComplexNormingCoverage
import Sigma.ComplexSelectedFamilyCoefficients
import Sigma.ComplexDistinguishedVectors

/-! The distinguished split vector at the stage covering a selected norming
sequence. Its evaluations are exactly the atomic differences controlled by
the three-level choice. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

def ComplexEnumeratedConstruction.choice (D : ComplexEnumeratedConstruction) :
    (side : Bool) → (a : ConstructionIndex) →
      ComplexThreeLevelChoice (complexCodeAtomicRows side (D.codeAtSide side a)) (D.stock a)
  | false, a => (D.data a).choices.1
  | true, a => (D.data a).choices.2

theorem ComplexEnumeratedConstruction.choice_piece (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (bit : Bool) :
    (D.choice side a).piece bit = (D.familyEquiv side (a,bit)).val := by
  cases side <;> cases bit <;> rfl

theorem ComplexEnumeratedConstruction.codeAtSide_supported (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (n : ℕ) (s bit : Bool) (i : ConstructionIndex) (hi : a ≤ i) :
    D.codeAtSide side a n (familyAtom s bit i) = 0 := by
  cases side
  · exact D.left_supported a n s bit i hi
  · exact D.right_supported a n s bit i hi

def ComplexEnumeratedConstruction.distinguishedVector (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) : ComplexFinalCandidate D side :=
  (0,complexSplitVector (D.baseSets side) (D.splitSets side) (D.splits side) a)

theorem ComplexEnumeratedConstruction.component_family_evaluation (D : ComplexEnumeratedConstruction)
    (side : Bool) (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) (i : ConstructionIndex × Bool) :
    (φ.comp (D.sideInjection side))
      ⟨complexCharacteristic (D.familyEquiv side i).val,complexCharacteristic_mem_ComplexJL (D.familyEquiv side i).property⟩ =
      (∑' p : (D.familyEquiv side i).val, D.coefficients φ (side,.inl p.val)) +
        D.coefficients φ (side,.inr (.inl i)) := by
  simp only [D.coefficients_side]
  exact complexIndexedJLDual_family (D.family_almostDisjoint side) (D.family_infinite side)
    (D.familyEquiv side) (φ.comp (D.sideInjection side)) i

theorem ComplexEnumeratedConstruction.selected_family_evaluation (D : ComplexEnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (φ : ℕ → ComplexFinalJLProduct D →L[ℂ] ℂ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (φ n)) (n : ℕ) (bit : Bool) :
    (φ n).comp (D.sideInjection side)
      ⟨complexCharacteristic (D.familyEquiv side (a,bit)).val,
        complexCharacteristic_mem_ComplexJL (D.familyEquiv side (a,bit)).property⟩ =
      complexMass (complexCodeAtomicRows side (D.codeAtSide side a) n) (D.choice side a |>.piece bit) := by
  rw [D.component_family_evaluation]
  have hz := D.codeAtSide_supported side a n side bit a le_rfl
  rw [hcode] at hz
  change D.coefficients (φ n) (side,.inr (.inl (a,bit))) = 0 at hz
  rw [hz,add_zero,D.choice_piece]
  unfold complexMass
  apply tsum_congr
  intro p
  rw [complexCodeAtomicRows_apply,hcode]

theorem ComplexEnumeratedConstruction.selected_vector_evaluation (D : ComplexEnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ)
    (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (n : ℕ) : e (k n) (D.distinguishedVector side a) =
      complexMass (complexCodeAtomicRows side (D.codeAtSide side a) n) (D.choice side a).Z -
        complexMass (complexCodeAtomicRows side (D.codeAtSide side a) n)
          (cylinder (D.choice side a).J₁ \ (D.choice side a).Z) := by
  let φ := D.extendCrossedFunctional side (e (k n))
  let ψ := φ.comp (D.sideInjection side)
  have h (bit : Bool) := D.selected_family_evaluation side a
    (fun n => D.extendCrossedFunctional side (e (k n))) hcode n bit
  have heq : ψ (⟨complexCharacteristic (D.familyEquiv side (a,false)).val,
        complexCharacteristic_mem_ComplexJL (D.familyEquiv side (a,false)).property⟩ -
      ⟨complexCharacteristic (D.familyEquiv side (a,true)).val,
        complexCharacteristic_mem_ComplexJL (D.familyEquiv side (a,true)).property⟩) =
      e (k n) (D.distinguishedVector side a) := by
    change e (k n) (D.crossedProjection side (D.sideInjection side _)) = _
    rw [D.crossedProjection_injection]
    have hv := D.antisymmetricProjection_of_mem side
      (complexSplitVector (D.baseSets side) (D.splitSets side) (D.splits side) a)
    change D.antisymmetricProjection side
      (⟨complexCharacteristic (D.familyEquiv side (a,false)).val,
          complexCharacteristic_mem_ComplexJL (D.familyEquiv side (a,false)).property⟩ -
       ⟨complexCharacteristic (D.familyEquiv side (a,true)).val,
          complexCharacteristic_mem_ComplexJL (D.familyEquiv side (a,true)).property⟩) = _ at hv
    rw [hv]
    rfl
  rw [← heq,map_sub,h false,h true]
  rfl

theorem ComplexEnumeratedConstruction.selected_three_levels (D : ComplexEnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ)
    (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n)))) :
    let d := D.choice side a
    0 < d.delta ∧ 11*d.delta < ‖d.a‖ ∧
    (∀ n ∈ d.J₂, ‖e (k n) (D.distinguishedVector side a) - 2*d.a‖ < 3*d.delta) ∧
    (∀ n ∈ d.J₁ \ d.J₂, ‖e (k n) (D.distinguishedVector side a) - (-(2*d.a))‖ < 3*d.delta) ∧
    (∀ n ∈ d.J₀ \ d.J₁, ‖e (k n) (D.distinguishedVector side a)‖ < 3*d.delta) := by
  let d := D.choice side a
  refine ⟨d.delta_pos,by linarith [d.delta_small,d.lower_a],?_,?_,?_⟩
  · intro n hn
    rw [D.selected_vector_evaluation side a e k hcode]
    exact d.positive_level n hn
  · intro n hn
    rw [D.selected_vector_evaluation side a e k hcode,sub_neg_eq_add]
    exact d.negative_level n hn
  · intro n hn
    rw [D.selected_vector_evaluation side a e k hcode]
    exact d.zero_level n hn

end SigmaNonprimarity


