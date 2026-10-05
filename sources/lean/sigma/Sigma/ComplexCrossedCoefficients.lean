import Sigma.ComplexCrossedProjection
import Sigma.ComplexFlipCoefficients
import Sigma.ComplexSingletonCoefficients
import Sigma.ComplexDesiredProperty

/-! Norming sequences on either crossed summand yield codes in the exact
admissible class enumerated by the construction. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem ComplexEnumeratedConstruction.extendedCoefficients_flip (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients (D.extendCrossedFunctional side φ) (side,indexedAtomFlip p) =
      -D.coefficients (D.extendCrossedFunctional side φ) (side,p) := by
  rw [D.coefficients_side,D.coefficients_side]
  exact D.indexedDual_antisymmetric side _ (D.extendCrossedFunctional_antisymmetric side φ) p

theorem ComplexEnumeratedConstruction.extendedCoefficients_infinity (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) :
    D.coefficients (D.extendCrossedFunctional side φ) (side,.inr (.inr ())) = 0 := by
  rw [D.coefficients_side]
  exact D.indexedDual_infinity_zero side _ (D.extendCrossedFunctional_antisymmetric side φ)

def complexCrossedFibreVector (D : ComplexEnumeratedConstruction) (side : Bool) (n : ℕ) : ComplexFinalCandidate D side :=
  (0,complexFibreVector (D.family side) n)

theorem complexCrossedFibreVector_norm (D : ComplexEnumeratedConstruction) (side : Bool) (n : ℕ) :
    ‖complexCrossedFibreVector D side n‖ = 1 := by
  change max ‖(0 : ComplexCylinderJL (cylinderFamily (D.baseSets (!side))))‖ ‖complexFibreVector (D.family side) n‖ = 1
  change max ‖(0 : ComplexAmbient)‖ ‖complexFibreVector (D.family side) n‖ = 1
  rw [norm_zero,complexFibreVector_norm]
  norm_num

theorem ComplexEnumeratedConstruction.antisymmetricProjection_of_mem (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : complexAntisymmetricJL (D.family side)) : D.antisymmetricProjection side ⟨f.val,f.property.1⟩ = f := by
  apply Subtype.ext
  change f.val - complexAverage f.val = f.val
  rw [show complexAverage f.val = 0 from f.property.2,sub_zero]

theorem ComplexEnumeratedConstruction.crossedFibre_evaluation (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) (n : ℕ) :
    φ (complexCrossedFibreVector D side n) =
      2 * D.coefficients (D.extendCrossedFunctional side φ) (side,.inl (n,false)) := by
  let ψ := (D.extendCrossedFunctional side φ).comp (D.sideInjection side)
  have heval : ψ (⟨complexCharacteristic {(n,false)},complexCharacteristic_singleton_mem_ComplexJL _ _⟩ -
      ⟨complexCharacteristic {(n,true)},complexCharacteristic_singleton_mem_ComplexJL _ _⟩) = φ (complexCrossedFibreVector D side n) := by
    change φ (D.crossedProjection side (D.sideInjection side _)) = _
    rw [D.crossedProjection_injection]
    have h := D.antisymmetricProjection_of_mem side (complexFibreVector (D.family side) n)
    change D.antisymmetricProjection side
      (⟨complexCharacteristic {(n,false)},complexCharacteristic_singleton_mem_ComplexJL _ _⟩ -
        ⟨complexCharacteristic {(n,true)},complexCharacteristic_singleton_mem_ComplexJL _ _⟩) = _ at h
    rw [h]
    rfl
  rw [D.coefficients_side]
  change φ (complexCrossedFibreVector D side n) =
    2 * complexIndexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) ψ (.inl (n,false))
  rw [← heval,map_sub,← complexIndexedJLDual_singleton (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side),
    ← complexIndexedJLDual_singleton (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side)]
  have ha := D.indexedDual_antisymmetric side ψ (D.extendCrossedFunctional_antisymmetric side φ) (.inl (n,false))
  change complexIndexedJLDualEquiv _ _ _ ψ (.inl (n,true)) = -complexIndexedJLDualEquiv _ _ _ ψ (.inl (n,false)) at ha
  rw [ha]
  ring

theorem ComplexEnumeratedConstruction.extendedRows_admissible (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hdiag : ∀ n, δ ≤ ‖φ n (complexCrossedFibreVector D side n)‖) :
    ComplexFullCodeAdmissible side (fun n => D.coefficients (D.extendCrossedFunctional side (φ n))) := by
  refine ⟨?_,?_,?_,?_,δ/2,by positivity,?_⟩
  · intro n
    rw [D.coefficients_norm]
    exact (D.extendCrossedFunctional_norm_le side (φ n)).trans (hφ n)
  · intro n k
    exact D.extendedCoefficients_flip side (φ n) (.inl (k,true))
  · intro n i
    exact D.extendedCoefficients_flip side (φ n) (.inr (.inl (i,true)))
  · intro n
    exact D.extendedCoefficients_infinity side (φ n)
  · intro n
    have h := hdiag n
    rw [D.crossedFibre_evaluation,norm_mul,Complex.norm_ofNat] at h
    linarith

theorem ComplexEnumeratedConstruction.normingRows_admissible (D : ComplexEnumeratedConstruction) (side : Bool)
    (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ) (he : IsComplexNorming e) :
    ∃ k : ℕ → ℕ, ComplexFullCodeAdmissible side
      (fun n => D.coefficients (D.extendCrossedFunctional side (e (k n)))) := by
  obtain ⟨c,hc⟩ := he
  obtain ⟨k,hk⟩ := complex_select_large_evaluations hc (complexCrossedFibreVector D side) (complexCrossedFibreVector_norm D side)
  exact ⟨k,D.extendedRows_admissible side (fun n => e (k n)) (fun n => hc.2.2.1 (k n))
    (half_pos hc.1) (fun n => (hk n).le)⟩

end SigmaNonprimarity


