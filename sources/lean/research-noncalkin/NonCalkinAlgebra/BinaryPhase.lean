import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.BinaryPhase

/-- The complex sign character of the additive group Z/2Z. -/
def phase (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]
@[simp] theorem phase_one : phase 1 = -1 := by norm_num [phase]

theorem phase_add (a b : ZMod 2) : phase (a + b) = phase a * phase b := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  fin_cases a <;> fin_cases b <;> simp [phase, one_add_one_eq_two, h2]

@[simp] theorem norm_phase (a : ZMod 2) : ‖phase a‖ = 1 := by
  unfold phase
  split_ifs <;> simp

theorem phase_ne_zero (a : ZMod 2) : phase a ≠ 0 := by
  intro h
  have := norm_phase a
  rw [h, norm_zero] at this
  exact zero_ne_one this

@[simp] theorem phase_mul_self (a : ZMod 2) : phase a * phase a = 1 := by
  unfold phase
  split_ifs <;> norm_num

@[simp] theorem star_phase (a : ZMod 2) : star (phase a) = phase a := by
  unfold phase
  split_ifs <;> simp

theorem phase_injective : Function.Injective phase := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (norm_num [phase] at h)

end NonCalkinAlgebra.BinaryPhase
