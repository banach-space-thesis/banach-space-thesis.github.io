import BanachIsometric.SphereRepetitionPositiveDerivative

/-! Actual positive regularity of the raw repetition cone at the chosen
non-pole sphere fiber, transported back to the original Euclidean norm. -/

namespace BanachIsometric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem differentiableAt_of_coordinateMapConjugate (e : E ≃L[ℝ] F) (f : E → E) (x : E)
    (h : DifferentiableAt ℝ (coordinateMapConjugate e f) (e x)) :
    DifferentiableAt ℝ f x := by
  have h' := e.symm.differentiableAt.comp x (h.comp x e.differentiableAt)
  simpa only [Function.comp_def, coordinateMapConjugate, e.symm_apply_apply] using h'

namespace SphereGenerator

open scoped Topology Topology.Homotopy unitInterval

theorem unitSphereCone_repetition_positive_on_axis_fiber (n d : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (w : Sph (n + 1)) (hw : sphereRepetition n d w = axisSphereTarget n) :
    DifferentiableAt ℝ (unitSphereCone (sphereRepetition n d)) (ρ • w.val) ∧
      0 < (fderiv ℝ (unitSphereCone (sphereRepetition n d)) (ρ • w.val)).det := by
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n w
  have hu : repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d u = axisSphereTarget n := by
    have he := congrArg (fun f : C((Fin (n + 1) → unitInterval), Sph (n + 1)) => f u)
      (sphereRepetition_comp_cubeToSphere n d)
    exact he.symm.trans hw
  have h := sphereRepetitionCone_positive_at_axis_fiber n d ρ hρ ⟨u, hu⟩
  rw [cubeSphereConeChart_eq_raw] at h
  refine ⟨differentiableAt_of_coordinateMapConjugate (euclideanCoordinates (n + 2)) _ _ h.1, ?_⟩
  have he := det_fderiv_coordinateConjugate (euclideanCoordinates (n + 2))
    (unitSphereCone (sphereRepetition n d)) (ρ • (cubeToSphere (n + 1) u).val)
  exact he ▸ h.2

end SphereGenerator
end BanachIsometric
