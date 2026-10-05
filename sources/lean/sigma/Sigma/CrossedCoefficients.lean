import Sigma.CrossedProjection
import Sigma.FlipCoefficients
import Sigma.SingletonCoefficients
import ThesisCommon.Analysis.NormingSequence

/-! Norming sequences on either crossed summand yield codes in the exact
admissible class enumerated by the construction. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

theorem EnumeratedConstruction.extendedCoefficients_flip (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients (D.extendCrossedFunctional side φ) (side,indexedAtomFlip p) =
      -D.coefficients (D.extendCrossedFunctional side φ) (side,p) := by
  rw [D.coefficients_side,D.coefficients_side]
  exact D.indexedDual_antisymmetric side _ (D.extendCrossedFunctional_antisymmetric side φ) p

theorem EnumeratedConstruction.extendedCoefficients_infinity (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) :
    D.coefficients (D.extendCrossedFunctional side φ) (side,.inr (.inr ())) = 0 := by
  rw [D.coefficients_side]
  exact D.indexedDual_infinity_zero side _ (D.extendCrossedFunctional_antisymmetric side φ)

def crossedFibreVector (D : EnumeratedConstruction) (side : Bool) (n : ℕ) : FinalCandidate D side :=
  (0,fibreVector (D.family side) n)

theorem crossedFibreVector_norm (D : EnumeratedConstruction) (side : Bool) (n : ℕ) :
    ‖crossedFibreVector D side n‖ = 1 := by
  change max ‖(0 : CylinderJL (cylinderFamily (D.baseSets (!side))))‖ ‖fibreVector (D.family side) n‖ = 1
  change max ‖(0 : Ambient)‖ ‖fibreVector (D.family side) n‖ = 1
  rw [norm_zero,fibreVector_norm]
  norm_num

theorem EnumeratedConstruction.antisymmetricProjection_of_mem (D : EnumeratedConstruction) (side : Bool)
    (f : antisymmetricJL (D.family side)) : D.antisymmetricProjection side ⟨f.val,f.property.1⟩ = f := by
  apply Subtype.ext
  change f.val - average f.val = f.val
  rw [show average f.val = 0 from f.property.2,sub_zero]

theorem EnumeratedConstruction.crossedFibre_evaluation (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) (n : ℕ) :
    φ (crossedFibreVector D side n) =
      2 * D.coefficients (D.extendCrossedFunctional side φ) (side,.inl (n,false)) := by
  let ψ := (D.extendCrossedFunctional side φ).comp (D.sideInjection side)
  have heval : ψ (⟨characteristic {(n,false)},characteristic_singleton_mem_JL _ _⟩ -
      ⟨characteristic {(n,true)},characteristic_singleton_mem_JL _ _⟩) = φ (crossedFibreVector D side n) := by
    change φ (D.crossedProjection side (D.sideInjection side _)) = _
    rw [D.crossedProjection_injection]
    have h := D.antisymmetricProjection_of_mem side (fibreVector (D.family side) n)
    change D.antisymmetricProjection side
      (⟨characteristic {(n,false)},characteristic_singleton_mem_JL _ _⟩ -
        ⟨characteristic {(n,true)},characteristic_singleton_mem_JL _ _⟩) = _ at h
    rw [h]
    rfl
  rw [D.coefficients_side]
  change φ (crossedFibreVector D side n) =
    2 * indexedJLDualEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side) ψ (.inl (n,false))
  rw [← heval,map_sub,← indexedJLDual_singleton (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side),
    ← indexedJLDual_singleton (D.family_almostDisjoint side) (D.family_infinite side) (D.familyEquiv side)]
  have ha := D.indexedDual_antisymmetric side ψ (D.extendCrossedFunctional_antisymmetric side φ) (.inl (n,false))
  change indexedJLDualEquiv _ _ _ ψ (.inl (n,true)) = -indexedJLDualEquiv _ _ _ ψ (.inl (n,false)) at ha
  rw [ha]
  ring

theorem EnumeratedConstruction.extendedRows_admissible (D : EnumeratedConstruction) (side : Bool)
    (φ : ℕ → FinalCandidate D side →L[ℝ] ℝ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hdiag : ∀ n, δ ≤ |φ n (crossedFibreVector D side n)|) :
    FullCodeAdmissible side (fun n => D.coefficients (D.extendCrossedFunctional side (φ n))) := by
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
    rw [D.crossedFibre_evaluation,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith

theorem EnumeratedConstruction.normingRows_admissible (D : EnumeratedConstruction) (side : Bool)
    (e : ℕ → FinalCandidate D side →L[ℝ] ℝ) (he : IsNorming e) :
    ∃ k : ℕ → ℕ, FullCodeAdmissible side
      (fun n => D.coefficients (D.extendCrossedFunctional side (e (k n)))) := by
  obtain ⟨c,hc⟩ := he
  obtain ⟨k,hk⟩ := select_large_evaluations hc (crossedFibreVector D side) (crossedFibreVector_norm D side)
  exact ⟨k,D.extendedRows_admissible side (fun n => e (k n)) (fun n => hc.2.2.1 (k n))
    (half_pos hc.1) (fun n => (hk n).le)⟩

end SigmaNonprimarity
