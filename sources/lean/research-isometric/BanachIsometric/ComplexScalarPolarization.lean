import BanachIsometric.ComplexPolarization
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Algebraic complex reconstruction from a real quadratic form

The original complex action is fixed throughout. A real positive quadratic
form invariant under multiplication by `I` has a unique positive complex
Hermitian form with that diagonal. No norm or topology is introduced.
-/

namespace BanachIsometric

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X]
  [IsScalarTower ℝ ℂ X]

private theorem complex_smul_decompose (a : ℂ) (x : X) :
    a • x = a.re • x + a.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im a]
  rw [add_smul, mul_smul]
  change (algebraMap ℝ ℂ a.re) • x + (algebraMap ℝ ℂ a.im) • (Complex.I • x) = _
  rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]

/-- The complex part of the paper's scalar-polarisation lemma, proved
algebraically on the given module. Invariance under `I` alone suffices. -/
theorem existsUnique_complexHermitian_of_realQuadratic
    (q : QuadraticForm ℝ X) (hq : q.PosDef)
    (hI : ∀ x : X, q (Complex.I • x) = q x) :
    ∃! h : PositiveHermitianForm X, ∀ x, h.form x x = (q x : ℂ) := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let B : X →ₗ[ℝ] X →ₗ[ℝ] ℝ := QuadraticMap.associated q
  have hself : ∀ x : X, B x x = q x := QuadraticMap.associated_eq_self_apply ℝ q
  have hsym : ∀ x y : X, B x y = B y x := QuadraticMap.associated_isSymm ℝ q
  have hII (x : X) : Complex.I • (Complex.I • x) = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hinv (x y : X) : B (Complex.I • x) (Complex.I • y) = B x y := by
    have h := hI (x + y)
    rw [← hself, ← hself, smul_add] at h
    simp only [map_add, LinearMap.add_apply] at h
    have hx := hI x
    have hy := hI y
    rw [← hself, ← hself] at hx hy
    rw [hsym (Complex.I • y) (Complex.I • x), hsym y x] at h
    linarith
  have hskew (x y : X) : B (Complex.I • x) y = -B x (Complex.I • y) := by
    have h := hinv x (Complex.I • y)
    rw [hII, map_neg] at h
    linarith
  have hzero (x : X) : B x (Complex.I • x) = 0 := by
    have h := hskew x x
    rw [hsym (Complex.I • x) x] at h
    linarith
  let H : X → X → ℂ := fun x y => ⟨B x y, -B x (Complex.I • y)⟩
  have hHself (x : X) : H x x = (q x : ℂ) := by
    apply Complex.ext <;> simp [H, hself, hzero]
  let h : PositiveHermitianForm X :=
    { form := H
      conj_symm := by
        intro x y
        apply Complex.ext
        · exact hsym x y
        · change -(-B x (Complex.I • y)) = -B y (Complex.I • x)
          rw [hsym y (Complex.I • x), hskew]
      add_right := by
        intro x y z
        apply Complex.ext <;> simp [H, smul_add, map_add, add_comm]
      smul_right := by
        intro x y a
        have hIy : Complex.I • (a • y) = a.re • (Complex.I • y) - a.im • y := by
          rw [complex_smul_decompose a y, smul_add, smul_comm Complex.I a.re,
            smul_comm Complex.I a.im, hII, smul_neg, sub_eq_add_neg]
        apply Complex.ext
        · change B x (a • y) = a.re * B x y - a.im * (-B x (Complex.I • y))
          rw [complex_smul_decompose a y, map_add,
            (B x).map_smul a.re y, (B x).map_smul a.im (Complex.I • y)]
          simp only [smul_eq_mul]
          ring
        · change -B x (Complex.I • (a • y)) =
            a.re * (-B x (Complex.I • y)) + a.im * B x y
          rw [hIy, map_sub, (B x).map_smul a.re (Complex.I • y), (B x).map_smul a.im y]
          simp only [smul_eq_mul]
          ring
      self_im := by intro x; rw [hHself]; rfl
      self_nonneg := by
        intro x
        rw [hHself]
        exact hq.nonneg x
      self_pos := by
        intro x hx
        rw [hHself]
        exact hq x hx }
  refine ⟨h, hHself, ?_⟩
  intro k hk
  apply PositiveHermitianForm.eq_of_diagonal_eq
  intro x
  exact (hk x).trans (hHself x).symm

end BanachIsometric
