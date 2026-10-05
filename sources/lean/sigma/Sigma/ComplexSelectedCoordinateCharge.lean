import Sigma.ComplexNormingCoverage
import Sigma.CoordinateCharge

/-! Agreement on one copy of the paired base, with the other component zero. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem complexCharacteristic_empty : complexCharacteristic ∅ = (0 : ComplexAmbient) := by
  ext p
  simp

theorem ComplexEnumeratedConstruction.functionalCharge_oneCopy (D : ComplexEnumeratedConstruction)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (copy : Bool) {A : Set Point}
    (hA : A ∈ generatedAlgebra (D.family copy)) :
    ∃ hmem : complexCharacteristic A ∈ ComplexJL (D.family copy),
      D.functionalCharge φ hφ (oneCopySet copy A) = φ (D.sideInjection copy ⟨complexCharacteristic A,hmem⟩) := by
  cases copy
  · obtain ⟨hmem,he,hh⟩ := D.functionalCharge_generated φ hφ hA BooleanSubalgebra.bot_mem
    have hz : (⟨complexCharacteristic ∅,he⟩ : ComplexJL (D.family true)) = 0 := Subtype.ext complexCharacteristic_empty
    change D.functionalCharge φ hφ (pairedBaseSet A ∅) =
      φ (⟨complexCharacteristic A,hmem⟩,⟨complexCharacteristic ∅,he⟩) at hh
    rw [hz] at hh
    refine ⟨hmem,?_⟩
    simpa only [pairedBaseSet,codedSet,Set.image_empty,Set.union_empty,hz,oneCopySet,
      Bool.false_eq_true,if_false,ComplexEnumeratedConstruction.sideInjection,ContinuousLinearMap.inl_apply] using hh
  · obtain ⟨he,hmem,hh⟩ := D.functionalCharge_generated φ hφ BooleanSubalgebra.bot_mem hA
    have hz : (⟨complexCharacteristic ∅,he⟩ : ComplexJL (D.family false)) = 0 := Subtype.ext complexCharacteristic_empty
    change D.functionalCharge φ hφ (pairedBaseSet ∅ A) =
      φ (⟨complexCharacteristic ∅,he⟩,⟨complexCharacteristic A,hmem⟩) at hh
    rw [hz] at hh
    refine ⟨hmem,?_⟩
    simpa only [pairedBaseSet,codedSet,Set.image_empty,Set.empty_union,hz,oneCopySet,
      if_true,ComplexEnumeratedConstruction.sideInjection,ContinuousLinearMap.inr_apply] using hh

theorem ComplexEnumeratedConstruction.selected_coordinate_charge (D : ComplexEnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ)
    (he : ∀ n, ‖e n‖ ≤ 1) (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (copy : Bool) {A : Set Point} (hA : A ∈ generatedAlgebra (D.family copy))
    (hmem : complexCharacteristic A ∈ ComplexJL (D.family copy)) (n : ℕ) :
    D.chargeAtSide side a n (oneCopySet copy A) =
      e (k n) (D.crossedProjection side (D.sideInjection copy ⟨complexCharacteristic A,hmem⟩)) := by
  have hu (n : ℕ) : ‖D.extendCrossedFunctional side (e (k n))‖ ≤ 1 :=
    (D.extendCrossedFunctional_norm_le side _).trans (he (k n))
  rw [D.chargeAtSide_agreement side a (fun n => D.extendCrossedFunctional side (e (k n))) hu hcode]
  obtain ⟨_,hh⟩ := D.functionalCharge_oneCopy _ (hu n) copy hA
  exact hh

end SigmaNonprimarity


