import ThesisCommon.Analysis.GowersMaureyOperatorOrbitApproximation
import ThesisCommon.Analysis.GowersMaureyWienerCompletion

/-! Every genuine bounded operator on the constructed shift space admits
finite-spread approximation in the actual source block seminorm. This
discharges, rather than assumes, the representation-completion premise. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finiteSpreadApproximable (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) : IsFiniteSpreadApproximable D T := by
  classical
  intro ε hε
  obtain ⟨m,_,V,hV,hbound⟩ := exists_operator_orbit_seminorm_approximation D ⊤
    (restrictOperatorToTop D T) (show 0 < ε/34 by positivity)
  rw [← finiteParameterOrbit_eq (fun z : ℕ × ℕ => (completedSpread D z.1 z.2).comp
    (⊤ : Submodule 𝕜 (ShiftSpace D)).subtypeL) (spreadParameterSquare m) (m : ℝ)] at hV
  obtain ⟨c,_,hc⟩ := hV
  refine ⟨spreadParameterSquare m,c,?_⟩
  change blockOperatorSeminorm D ⊤ (restrictOperatorToTop D
    (T-∑ z ∈ spreadParameterSquare m, c z • completedSpread D z.1 z.2)) < ε
  have he : restrictOperatorToTop D
      (T-∑ z ∈ spreadParameterSquare m, c z • completedSpread D z.1 z.2) =
      restrictOperatorToTop D T-V := by
    rw [← hc]
    simp only [map_sub,map_sum,map_smul]
    rfl
  rw [he]
  linarith

end ThesisCommon.GowersMaurey
