import Sigma.NormingCoverage

/-! Agreement on one copy of the paired base, with the other component zero. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

def oneCopySet (copy : Bool) (A : Set Point) : Set (ℕ ⊕ ℕ) :=
  if copy then Sum.inr '' codedSet A else Sum.inl '' codedSet A

theorem characteristic_empty : characteristic ∅ = (0 : Ambient) := by
  ext p
  simp

theorem EnumeratedConstruction.functionalCharge_oneCopy (D : EnumeratedConstruction)
    (φ : FinalJLProduct D →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (copy : Bool) {A : Set Point}
    (hA : A ∈ generatedAlgebra (D.family copy)) :
    ∃ hmem : characteristic A ∈ JL (D.family copy),
      D.functionalCharge φ hφ (oneCopySet copy A) = φ (D.sideInjection copy ⟨characteristic A,hmem⟩) := by
  cases copy
  · obtain ⟨hmem,he,hh⟩ := D.functionalCharge_generated φ hφ hA BooleanSubalgebra.bot_mem
    have hz : (⟨characteristic ∅,he⟩ : JL (D.family true)) = 0 := Subtype.ext characteristic_empty
    change D.functionalCharge φ hφ (pairedBaseSet A ∅) =
      φ (⟨characteristic A,hmem⟩,⟨characteristic ∅,he⟩) at hh
    rw [hz] at hh
    refine ⟨hmem,?_⟩
    simpa only [pairedBaseSet,codedSet,Set.image_empty,Set.union_empty,hz,oneCopySet,
      Bool.false_eq_true,if_false,EnumeratedConstruction.sideInjection,ContinuousLinearMap.inl_apply] using hh
  · obtain ⟨he,hmem,hh⟩ := D.functionalCharge_generated φ hφ BooleanSubalgebra.bot_mem hA
    have hz : (⟨characteristic ∅,he⟩ : JL (D.family false)) = 0 := Subtype.ext characteristic_empty
    change D.functionalCharge φ hφ (pairedBaseSet ∅ A) =
      φ (⟨characteristic ∅,he⟩,⟨characteristic A,hmem⟩) at hh
    rw [hz] at hh
    refine ⟨hmem,?_⟩
    simpa only [pairedBaseSet,codedSet,Set.image_empty,Set.empty_union,hz,oneCopySet,
      if_true,EnumeratedConstruction.sideInjection,ContinuousLinearMap.inr_apply] using hh

theorem EnumeratedConstruction.selected_coordinate_charge (D : EnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → FinalCandidate D side →L[ℝ] ℝ)
    (he : ∀ n, ‖e n‖ ≤ 1) (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (copy : Bool) {A : Set Point} (hA : A ∈ generatedAlgebra (D.family copy))
    (hmem : characteristic A ∈ JL (D.family copy)) (n : ℕ) :
    D.chargeAtSide side a n (oneCopySet copy A) =
      e (k n) (D.crossedProjection side (D.sideInjection copy ⟨characteristic A,hmem⟩)) := by
  have hu (n : ℕ) : ‖D.extendCrossedFunctional side (e (k n))‖ ≤ 1 :=
    (D.extendCrossedFunctional_norm_le side _).trans (he (k n))
  rw [D.chargeAtSide_agreement side a (fun n => D.extendCrossedFunctional side (e (k n))) hu hcode]
  obtain ⟨_,hh⟩ := D.functionalCharge_oneCopy _ (hu n) copy hA
  exact hh

end SigmaNonprimarity
