import SurveyStatements.P1Geometry
import Mathlib.Topology.Order.Compact

/-! Compactness of the phase circle and attainment of toroidal distance. -/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem isCompact_unitScalars : IsCompact unitScalars := by
  simpa [unitScalars, Metric.sphere, dist_zero_right] using isCompact_sphere (0 : ℂ) 1

/-- The phase infimum is attained, even when the ambient normed space is not
complete. This justifies choosing phases in the source's finite covers. -/
theorem exists_toroidalDistance_phase (x y : X) :
    ∃ θ ∈ unitScalars, toroidalDistance x y = ‖x - θ • y‖ := by
  have hcont : Continuous (fun θ : ℂ => ‖x - θ • y‖) :=
    (continuous_const.sub (continuous_id.smul continuous_const)).norm
  obtain ⟨θ, hθ, hmin⟩ := isCompact_unitScalars.exists_isMinOn
    ⟨1, one_mem_unitScalars⟩ hcont.continuousOn
  refine ⟨θ, hθ, le_antisymm (toroidalDistance_le_phase x y hθ) ?_⟩
  apply (le_toroidalDistance_iff _ _ _).mpr
  exact hmin

theorem toroidalDistance_le_iff_exists_phase (x y : X) (r : ℝ) :
    toroidalDistance x y ≤ r ↔ ∃ θ ∈ unitScalars, ‖x - θ • y‖ ≤ r := by
  constructor
  · intro h
    obtain ⟨θ, hθ, hd⟩ := exists_toroidalDistance_phase x y
    exact ⟨θ, hθ, by rwa [← hd]⟩
  · rintro ⟨θ, hθ, h⟩
    exact (toroidalDistance_le_phase x y hθ).trans h

end SurveyStatements.P1
