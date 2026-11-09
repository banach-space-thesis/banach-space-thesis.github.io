import BanachIsometric.QuaternionicPolarization
import BanachIsometric.FiniteConfigurations

/-!
# Gluing local right quaternionic Hermitian forms

The canonical polarisation formula identifies all local forms from their
diagonals, so three-vector containment gives a global Hermitian form. This is
an alternative to the global real Jordan--von Neumann/Cauchy--Schwarz argument
in the paper. The local geometric result remains an explicit premise.

The ambient right action is fixed by `Module Hᵐᵒᵖ E`. No norm, topology,
completeness, or ambient real scalar structure is required for this gluing.
-/

namespace BanachIsometric
namespace Quaternionic

open scoped Quaternion

variable {E : Type*} [AddCommGroup E] [Module Hᵐᵒᵖ E]

theorem HermitianForm.neg_right (h : HermitianForm E) (x y : E) :
    h.form x (-y) = -h.form x y := by
  simpa only [rightMul_neg_one, mul_neg_one] using h.mul_right x y (-1)

theorem HermitianForm.neg_left (h : HermitianForm E) (x y : E) :
    h.form (-x) y = -h.form x y := by
  simpa only [rightMul_neg_one, star_neg, star_one, neg_one_mul] using h.mul_left x y (-1)

theorem HermitianForm.sub_right (h : HermitianForm E) (x y z : E) :
    h.form x (y - z) = h.form x y - h.form x z := by
  rw [sub_eq_add_neg, h.add_right, h.neg_right, sub_eq_add_neg]

theorem HermitianForm.sub_left (h : HermitianForm E) (x y z : E) :
    h.form (x - y) z = h.form x z - h.form y z := by
  rw [sub_eq_add_neg, h.add_left, h.neg_left, sub_eq_add_neg]

/-- Real bilinear polarisation, expressed purely in terms of a diagonal. -/
noncomputable def realDiagonalPolar (q : E → ℝ) (x y : E) : ℝ :=
  (q (x + y) - q (x - y)) / 4

/-- The right quaternionic polarisation formula from a real diagonal. -/
noncomputable def quaternionPolar (q : E → ℝ) (x y : E) : H :=
  ⟨realDiagonalPolar q x y, realDiagonalPolar q (rightMul x i) y,
    realDiagonalPolar q (rightMul x j) y, realDiagonalPolar q (rightMul x k) y⟩

theorem HermitianForm.re_eq_realDiagonalPolar (h : HermitianForm E)
    {q : E → ℝ} (hq : ∀ x, h.form x x = (q x : H)) (x y : E) :
    (h.form x y).re = realDiagonalPolar q x y := by
  have hsum : (q (x + y) : H) =
      h.form x x + h.form x y + (h.form y x + h.form y y) := by
    rw [← hq, h.add_left, h.add_right, h.add_right]
  have hdiff : (q (x - y) : H) =
      h.form x x - h.form x y - (h.form y x - h.form y y) := by
    rw [← hq, h.sub_left, h.sub_right, h.sub_right]
  have hsr := congrArg QuaternionAlgebra.re hsum
  have hdr := congrArg QuaternionAlgebra.re hdiff
  simp only [Quaternion.re_add, Quaternion.re_sub, Quaternion.re_coe] at hsr hdr
  have hswap : (h.form y x).re = (h.form x y).re := by
    rw [← h.star_symm x y, Quaternion.re_star]
  unfold realDiagonalPolar
  linarith

/-- Every right Hermitian form is recovered from its diagonal by this same
formula; no prior real bilinear form is assumed in this statement. -/
theorem HermitianForm.form_eq_quaternionPolar (h : HermitianForm E)
    {q : E → ℝ} (hq : ∀ x, h.form x x = (q x : H)) (x y : E) :
    h.form x y = quaternionPolar q x y := by
  apply Quaternion.ext
  · exact h.re_eq_realDiagonalPolar hq x y
  · have hh := h.re_eq_realDiagonalPolar hq (rightMul x i) y
    rw [h.mul_left] at hh
    simpa [Quaternion.re_mul, i] using hh
  · have hh := h.re_eq_realDiagonalPolar hq (rightMul x j) y
    rw [h.mul_left] at hh
    simpa [Quaternion.re_mul, j] using hh
  · have hh := h.re_eq_realDiagonalPolar hq (rightMul x k) y
    rw [h.mul_left] at hh
    simpa [Quaternion.re_mul, k] using hh

/-- Existence of a positive right quaternionic Hermitian form with the specified
real diagonal. The module structures in this definition are the original ones. -/
def HasHermitianDiagonal (q : E → ℝ) : Prop :=
  ∃ h : HermitianForm E, (∀ x, h.form x x = (q x : H)) ∧ h.IsPositiveDefinite

/-- The square formulation used for gauges and norms in the paper. -/
def HasHermitianSquare (p : E → ℝ) : Prop := HasHermitianDiagonal (fun x => p x ^ 2)

@[simp] theorem quaternionPolar_submodule (q : E → ℝ) (Y : Submodule Hᵐᵒᵖ E)
    (x y : Y) : quaternionPolar (fun z : Y => q z.val) x y =
      quaternionPolar q x.val y.val := rfl

theorem HermitianForm.form_eq_ambient_quaternionPolar {q : E → ℝ}
    (Y : Submodule Hᵐᵒᵖ E) (h : HermitianForm Y)
    (hq : ∀ y : Y, h.form y y = (q y.val : H)) (x y : Y) :
    h.form x y = quaternionPolar q x.val y.val := by
  simpa only [quaternionPolar_submodule] using h.form_eq_quaternionPolar hq x y

/-- Positive local Hermitian diagonals on all subspaces of one available right
dimension at least three glue to a positive global Hermitian diagonal.
The ambient right dimension may be infinite. -/
theorem hasHermitianDiagonal_of_local {q : E → ℝ} (m : ℕ) (hm3 : 3 ≤ m)
    (hm : (m : Cardinal) ≤ Module.rank Hᵐᵒᵖ E)
    (hlocal : ∀ Y : Submodule Hᵐᵒᵖ E, FiniteDimensional Hᵐᵒᵖ Y →
      Module.finrank Hᵐᵒᵖ Y = m → HasHermitianDiagonal (fun y : Y => q y.val)) :
    HasHermitianDiagonal q := by
  have hdiag (x : E) : quaternionPolar q x x = (q x : H) := by
    obtain ⟨Y, hx, _, _, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x 0 0
    obtain ⟨h, hp, _⟩ := hlocal Y hfinite hdim
    rw [← h.form_eq_ambient_quaternionPolar Y hp (⟨x, hx⟩ : Y) (⟨x, hx⟩ : Y)]
    exact hp ⟨x, hx⟩
  have hconj (x y : E) : star (quaternionPolar q x y) = quaternionPolar q y x := by
    obtain ⟨Y, hx, hy, _, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x y 0
    obtain ⟨h, hp, _⟩ := hlocal Y hfinite hdim
    have hform := h.form_eq_ambient_quaternionPolar Y hp
    simpa only [hform] using h.star_symm (⟨x, hx⟩ : Y) (⟨y, hy⟩ : Y)
  have hadd (x y z : E) : quaternionPolar q x (y + z) =
      quaternionPolar q x y + quaternionPolar q x z := by
    obtain ⟨Y, hx, hy, hz, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x y z
    obtain ⟨h, hp, _⟩ := hlocal Y hfinite hdim
    have hform := h.form_eq_ambient_quaternionPolar Y hp
    simpa only [hform] using h.add_right (⟨x, hx⟩ : Y) (⟨y, hy⟩ : Y) (⟨z, hz⟩ : Y)
  have hmul (x y : E) (a : H) : quaternionPolar q x (rightMul y a) =
      quaternionPolar q x y * a := by
    obtain ⟨Y, hx, hy, _, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x y 0
    obtain ⟨h, hp, _⟩ := hlocal Y hfinite hdim
    have hform := h.form_eq_ambient_quaternionPolar Y hp
    simpa only [hform] using h.mul_right (⟨x, hx⟩ : Y) (⟨y, hy⟩ : Y) a
  have hpos (x : E) (hx0 : x ≠ 0) : 0 < (quaternionPolar q x x).re := by
    obtain ⟨Y, hx, _, _, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x 0 0
    obtain ⟨h, hp, hpositive⟩ := hlocal Y hfinite hdim
    have hform := h.form_eq_ambient_quaternionPolar Y hp
    have hnonzero : (⟨x, hx⟩ : Y) ≠ 0 := fun heq => hx0 (congrArg Subtype.val heq)
    simpa only [hform] using hpositive (⟨x, hx⟩ : Y) hnonzero
  exact ⟨{
    form := quaternionPolar q
    add_right := hadd
    mul_right := hmul
    star_symm := hconj
  }, hdiag, hpos⟩

/-- The gauge-square specialization, with all local geometric obligations
retained explicitly. -/
theorem hasHermitianSquare_of_local {p : E → ℝ} (m : ℕ) (hm3 : 3 ≤ m)
    (hm : (m : Cardinal) ≤ Module.rank Hᵐᵒᵖ E)
    (hlocal : ∀ Y : Submodule Hᵐᵒᵖ E, FiniteDimensional Hᵐᵒᵖ Y →
      Module.finrank Hᵐᵒᵖ Y = m → HasHermitianSquare (fun y : Y => p y.val)) :
    HasHermitianSquare p :=
  hasHermitianDiagonal_of_local m hm3 hm hlocal

end Quaternionic
end BanachIsometric
