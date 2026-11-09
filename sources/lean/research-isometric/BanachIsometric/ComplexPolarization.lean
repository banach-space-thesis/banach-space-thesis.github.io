import BanachIsometric.Functional
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic complex polarization without an ambient norm

The canonical formula depends only on the diagonal of the form. Expanding the
four diagonal values directly avoids installing an auxiliary normed-space
structure, and therefore retains the original algebraic complex action.
-/

namespace BanachIsometric

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

namespace PositiveHermitianForm

theorem map_add_left (h : PositiveHermitianForm X) (x y z : X) :
    h.form (x + y) z = h.form x z + h.form y z := by
  calc
    h.form (x + y) z = star (h.form z (x + y)) := (h.conj_symm z _).symm
    _ = star (h.form z x + h.form z y) := congrArg star (h.add_right z x y)
    _ = h.form x z + h.form y z := by rw [star_add, h.conj_symm, h.conj_symm]

theorem map_smul_left (h : PositiveHermitianForm X) (a : ℂ) (x y : X) :
    h.form (a • x) y = star a * h.form x y := by
  calc
    h.form (a • x) y = star (h.form y (a • x)) := (h.conj_symm y _).symm
    _ = star (a * h.form y x) := congrArg star (h.smul_right y x a)
    _ = star a * h.form x y := by rw [star_mul, h.conj_symm, mul_comm]

theorem map_sub_left (h : PositiveHermitianForm X) (x y z : X) :
    h.form (x - y) z = h.form x z - h.form y z := by
  rw [sub_eq_add_neg, h.map_add_left, ← neg_one_smul ℂ y, h.map_smul_left]
  simp [sub_eq_add_neg]

theorem map_sub_right (h : PositiveHermitianForm X) (x y z : X) :
    h.form x (y - z) = h.form x y - h.form x z := by
  rw [sub_eq_add_neg, h.add_right, ← neg_one_smul ℂ z, h.smul_right]
  simp [sub_eq_add_neg]

/-- Complex polarization, proved by direct expansion of the Hermitian laws.
The diagonal may be specified by an arbitrary real homogeneous function later. -/
theorem form_eq_diagonal_polarization (h : PositiveHermitianForm X) (x y : X) :
    h.form x y =
      (h.form (x + y) (x + y) - h.form (x - y) (x - y) +
        (h.form (x - Complex.I • y) (x - Complex.I • y) -
          h.form (x + Complex.I • y) (x + Complex.I • y)) * Complex.I) / 4 := by
  simp only [h.map_add_left, h.add_right, h.map_sub_left, h.map_sub_right,
    h.map_smul_left, h.smul_right, Complex.star_def, Complex.conj_I]
  linear_combination (h.form x y - h.form y x) / 2 * Complex.I_mul_I

/-- Equal diagonals force equal forms, using only the algebraic Hermitian laws. -/
theorem form_eq_of_diagonal_eq (h k : PositiveHermitianForm X)
    (hd : ∀ x, h.form x x = k.form x x) : h.form = k.form := by
  funext x y
  rw [h.form_eq_diagonal_polarization, k.form_eq_diagonal_polarization]
  simp only [hd]

theorem eq_of_diagonal_eq (h k : PositiveHermitianForm X)
    (hd : ∀ x, h.form x x = k.form x x) : h = k := by
  have hf := h.form_eq_of_diagonal_eq k hd
  cases h
  cases k
  cases hf
  rfl

end PositiveHermitianForm

/-- The norm-free canonical complex polarization of a real-valued function. -/
noncomputable def complexPolar (p : X → ℝ) (x y : X) : ℂ :=
  (((p (x + y) ^ 2 : ℝ) : ℂ) - ((p (x - y) ^ 2 : ℝ) : ℂ) +
    (((p (x - Complex.I • y) ^ 2 : ℝ) : ℂ) -
      ((p (x + Complex.I • y) ^ 2 : ℝ) : ℂ)) * Complex.I) / 4

theorem PositiveHermitianForm.form_eq_complexPolar (h : PositiveHermitianForm X)
    {p : X → ℝ} (hp : ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ)) (x y : X) :
    h.form x y = complexPolar p x y := by
  rw [h.form_eq_diagonal_polarization]
  simp only [hp, complexPolar]

end BanachIsometric
