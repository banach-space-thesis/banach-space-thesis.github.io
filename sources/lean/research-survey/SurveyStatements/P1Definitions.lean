import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Definitions for the toroidal Elton–Odell theorem. -/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The complex scalars of modulus one. -/
def unitScalars : Set ℂ := {θ | ‖θ‖ = 1}

/-- Infimum of the distances over all complex phases. -/
def toroidalDistance (x y : X) : ℝ :=
  sInf {r : ℝ | ∃ θ ∈ unitScalars, r = ‖x - θ • y‖}

/-- Separation by a common margin, for every pair and every complex phase. -/
def IsToroidallySeparated (ε : ℝ) (x : ℕ → X) : Prop :=
  ∀ n m : ℕ, n ≠ m → ∀ θ : ℂ, θ ∈ unitScalars →
    1 + ε ≤ ‖x n - θ • x m‖

end SurveyStatements.P1
