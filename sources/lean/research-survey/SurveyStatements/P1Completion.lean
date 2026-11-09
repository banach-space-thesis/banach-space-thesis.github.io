import SurveyStatements.P1Transfer
import Mathlib.Analysis.Normed.Module.Completion

/-! The completion-and-density reduction at the end of the source P1 proof. -/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Completion does not turn an infinite-dimensional space into a finite one. -/
theorem completion_infiniteDimensional (hX : ¬ FiniteDimensional ℂ X) :
    ¬ FiniteDimensional ℂ (UniformSpace.Completion X) := by
  intro h
  letI := h
  exact hX (FiniteDimensional.of_injective
    (UniformSpace.Completion.toComplₗᵢ : X →ₗᵢ[ℂ] UniformSpace.Completion X).toLinearMap
    (UniformSpace.Completion.toComplₗᵢ : X →ₗᵢ[ℂ] UniformSpace.Completion X).injective)

/-- A toroidally separated unit sequence in the completion gives one in `X`. -/
theorem completion_separation_transfer
    (h : ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → UniformSpace.Completion X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℕ → X,
      (∀ n, ‖x n‖ = 1) ∧ IsToroidallySeparated ε x := by
  obtain ⟨ε, hε, x, hx, hs⟩ := h
  exact denseRange_separation_transfer
    (UniformSpace.Completion.toComplₗᵢ : X →ₗᵢ[ℂ] UniformSpace.Completion X)
    UniformSpace.Completion.denseRange_coe hε hx hs

end SurveyStatements.P1
