import Sigma.ComplexReducedCoefficients

/-! The dual of either actual crossed summand is linearly homeomorphic to
an ell-one space. Both inverses are constructed from atomic coefficients. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem ComplexEnumeratedConstruction.reducedCoefficients_injective (D : ComplexEnumeratedConstruction) (side : Bool) :
    Function.Injective (D.reducedCoefficients side) := by
  intro φ ψ h
  have hpair (copy : Bool) (q : ℕ ⊕ ConstructionIndex) :
      D.coefficients (D.extendCrossedFunctional side φ) (copy,pairedAtom q false) =
      D.coefficients (D.extendCrossedFunctional side ψ) (copy,pairedAtom q false) := by
    have ht := congrArg (fun c : lp (fun _ : ReducedAtom => ℂ) 1 => c (.inl (copy,q))) h
    dsimp only at ht
    rw [D.reducedCoefficients_pair,D.reducedCoefficients_pair] at ht
    linear_combination (1/2 : ℂ) * ht
  have htrue (copy : Bool) (q : ℕ ⊕ ConstructionIndex) :
      D.coefficients (D.extendCrossedFunctional side φ) (copy,pairedAtom q true) =
      D.coefficients (D.extendCrossedFunctional side ψ) (copy,pairedAtom q true) := by
    by_cases hc : copy = side
    · subst copy
      have hφ := D.extendedCoefficients_flip side φ (pairedAtom q false)
      have hψ := D.extendedCoefficients_flip side ψ (pairedAtom q false)
      simp only [pairedAtom_flip,Bool.not_false] at hφ hψ
      rw [hφ,hψ,hpair]
    · have hc' : copy = !side := by cases copy <;> cases side <;> simp_all
      subst copy
      have hφ := D.extendedCoefficients_other_flip side φ (pairedAtom q false)
      have hψ := D.extendedCoefficients_other_flip side ψ (pairedAtom q false)
      simp only [pairedAtom_flip,Bool.not_false] at hφ hψ
      rw [hφ,hψ,hpair]
  have hinf : D.coefficients (D.extendCrossedFunctional side φ) (!side,.inr (.inr ())) =
      D.coefficients (D.extendCrossedFunctional side ψ) (!side,.inr (.inr ())) := by
    have ht := congrArg (fun c : lp (fun _ : ReducedAtom => ℂ) 1 => c (.inr ())) h
    simpa only [D.reducedCoefficients_infinity] using ht
  have hext : D.extendCrossedFunctional side φ = D.extendCrossedFunctional side ψ := by
    apply D.fullCoefficientEquiv.injective
    change D.coefficients (D.extendCrossedFunctional side φ) = D.coefficients (D.extendCrossedFunctional side ψ)
    apply lp.ext
    funext ⟨copy,p⟩
    rcases p with ⟨n,bit⟩ | (⟨i,bit⟩ | ⟨⟩)
    · cases bit
      · exact hpair copy (.inl n)
      · exact htrue copy (.inl n)
    · cases bit
      · exact hpair copy (.inr i)
      · exact htrue copy (.inr i)
    · by_cases hc : copy = side
      · subst copy
        rw [D.extendedCoefficients_infinity,D.extendedCoefficients_infinity]
      · have hc' : copy = !side := by cases copy <;> cases side <;> simp_all
        subst copy
        exact hinf
  apply ContinuousLinearMap.ext
  intro f
  have ht := congrArg (fun θ : ComplexFinalJLProduct D →L[ℂ] ℂ => θ (D.crossedInjection side f)) hext
  change φ (D.crossedProjection side (D.crossedInjection side f)) =
    ψ (D.crossedProjection side (D.crossedInjection side f)) at ht
  simpa only [D.crossedProjection_rightInverse] using ht

theorem ComplexEnumeratedConstruction.reducedCoefficients_synthesize (D : ComplexEnumeratedConstruction) (side : Bool)
    (c : lp (fun _ : ReducedAtom => ℂ) 1) :
    D.reducedCoefficients side (D.synthesizeReduced side c) = c := by
  let φ := D.fullCoefficientEquiv.symm (lpExtend (𝕜 := ℂ) 1 (reducedAtomEmbedding side) c)
  have hc : D.coefficients φ = lpExtend (𝕜 := ℂ) 1 (reducedAtomEmbedding side) c :=
    D.fullCoefficientEquiv.apply_symm_apply _
  have himage (copy : Bool) (q : ℕ ⊕ ConstructionIndex) :
      lpExtend (𝕜 := ℂ) 1 (reducedAtomEmbedding side) c (copy,pairedAtom q false) = c (.inl (copy,q)) :=
    lpExtend_apply_image (reducedAtomEmbedding side) c (.inl (copy,q))
  apply lp.ext
  funext p
  rcases p with ⟨copy,q⟩ | ⟨⟩
  · rw [D.reducedCoefficients_pair]
    change 2 * D.coefficients (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side)))
      (copy,pairedAtom q false) = _
    by_cases hcopy : copy = side
    · subst copy
      rw [D.restrictedCoefficients_selected,hc,pairedAtom_flip]
      rw [himage,Bool.not_false,complexExtendReduced_pair_true]
      ring
    · have hcopy' : copy = !side := by cases copy <;> cases side <;> simp_all
      subst copy
      rw [D.restrictedCoefficients_other,hc,pairedAtom_flip]
      rw [himage,Bool.not_false,complexExtendReduced_pair_true]
      ring
  · rw [D.reducedCoefficients_infinity]
    change D.coefficients (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side)))
      (!side,.inr (.inr ())) = _
    rw [D.restrictedCoefficients_other,hc]
    have hi : indexedAtomFlip (.inr (.inr ())) = .inr (.inr ()) := rfl
    rw [hi]
    have hm : lpExtend (𝕜 := ℂ) 1 (reducedAtomEmbedding side) c (!side,.inr (.inr ())) = c (.inr ()) :=
      lpExtend_apply_image (reducedAtomEmbedding side) c (.inr ())
    rw [hm]
    ring

def ComplexEnumeratedConstruction.crossedDualLinearEquiv (D : ComplexEnumeratedConstruction) (side : Bool) :
    (ComplexFinalCandidate D side →L[ℂ] ℂ) ≃ₗ[ℂ] lp (fun _ : ReducedAtom => ℂ) 1 where
  toFun := D.reducedCoefficients side
  invFun := D.synthesizeReduced side
  left_inv _ := D.reducedCoefficients_injective side (D.reducedCoefficients_synthesize side _)
  right_inv := D.reducedCoefficients_synthesize side
  map_add' := D.reducedCoefficients_add side
  map_smul' := D.reducedCoefficients_smul side

def ComplexEnumeratedConstruction.crossedDualEquiv (D : ComplexEnumeratedConstruction) (side : Bool) :
    (ComplexFinalCandidate D side →L[ℂ] ℂ) ≃L[ℂ] lp (fun _ : ReducedAtom => ℂ) 1 :=
  LinearEquiv.toContinuousLinearEquivOfBounds (D.crossedDualLinearEquiv side) 3 1
    (D.reducedCoefficients_norm_le side)
    (fun c => by simpa using D.synthesizeReduced_norm_le side c)

end SigmaNonprimarity


