import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-!
# Quaternionic polarisation with the paper's right-module convention

A right quaternionic module is encoded as a left module over the opposite
quaternion algebra. The real scalar action is the given action, with its usual
scalar-tower compatibility. No topology, norm, or completeness is assumed.
-/

namespace BanachIsometric
namespace Quaternionic

open scoped Quaternion

abbrev H := Quaternion ℝ

def i : H := ⟨0, 1, 0, 0⟩
def j : H := ⟨0, 0, 1, 0⟩
def k : H := ⟨0, 0, 0, 1⟩

@[simp] theorem i_mul_i : i * i = -1 := by ext <;> norm_num [i]
@[simp] theorem j_mul_j : j * j = -1 := by ext <;> norm_num [j]
@[simp] theorem k_mul_k : k * k = -1 := by ext <;> norm_num [k]
@[simp] theorem i_mul_j : i * j = k := by ext <;> norm_num [i, j, k]
@[simp] theorem j_mul_i : j * i = -k := by ext <;> norm_num [i, j, k]
@[simp] theorem j_mul_k : j * k = i := by ext <;> norm_num [i, j, k]
@[simp] theorem k_mul_j : k * j = -i := by ext <;> norm_num [i, j, k]
@[simp] theorem k_mul_i : k * i = j := by ext <;> norm_num [i, j, k]
@[simp] theorem i_mul_k : i * k = -j := by ext <;> norm_num [i, j, k]

@[simp] theorem normSq_i : Quaternion.normSq i = 1 := by norm_num [Quaternion.normSq_def', i]
@[simp] theorem normSq_j : Quaternion.normSq j = 1 := by norm_num [Quaternion.normSq_def', j]
@[simp] theorem normSq_k : Quaternion.normSq k = 1 := by norm_num [Quaternion.normSq_def', k]

theorem decompose (a : H) :
    a = (a.re : H) + i * (a.imI : H) + j * (a.imJ : H) + k * (a.imK : H) := by
  ext <;> simp [i, j, k]

theorem mul_i (a : H) : a * i = ⟨-a.imI, a.re, a.imK, -a.imJ⟩ := by
  ext <;> simp [i]

theorem mul_j (a : H) : a * j = ⟨-a.imJ, -a.imK, a.re, a.imI⟩ := by
  ext <;> simp [j]

theorem mul_k (a : H) : a * k = ⟨-a.imK, a.imJ, -a.imI, a.re⟩ := by
  ext <;> simp [k]

variable {E : Type*} [AddCommGroup E] [Module Hᵐᵒᵖ E]

/-- Right quaternion multiplication, represented by the opposite scalar action. -/
def rightMul (x : E) (a : H) : E := MulOpposite.op a • x

@[simp] theorem rightMul_one (x : E) : rightMul x 1 = x := by simp [rightMul]
@[simp] theorem rightMul_neg_one (x : E) : rightMul x (-1) = -x := by simp [rightMul]
@[simp] theorem rightMul_neg (x : E) (a : H) : rightMul x (-a) = -rightMul x a := by
  simp [rightMul]
@[simp] theorem rightMul_add (x : E) (a b : H) :
    rightMul x (a + b) = rightMul x a + rightMul x b := by simp [rightMul, add_smul]
@[simp] theorem rightMul_add_left (x y : E) (a : H) :
    rightMul (x + y) a = rightMul x a + rightMul y a := by simp [rightMul, smul_add]

theorem rightMul_assoc (x : E) (a b : H) :
    rightMul (rightMul x a) b = rightMul x (a * b) := by
  simp [rightMul, smul_smul, MulOpposite.op_mul]

variable [Module ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E]

@[simp] theorem rightMul_real (x : E) (r : ℝ) : rightMul x (r : H) = r • x := by
  change (algebraMap ℝ Hᵐᵒᵖ r) • x = r • x
  exact algebraMap_smul Hᵐᵒᵖ r x

theorem rightMul_decompose (x : E) (a : H) :
    rightMul x a = a.re • x + a.imI • rightMul x i +
      a.imJ • rightMul x j + a.imK • rightMul x k := by
  conv_lhs => rw [decompose a]
  simp only [rightMul_add, ← rightMul_assoc, rightMul_real]

/-- Hermitian forms for right modules: right linear in the second variable and
conjugate linear in the first. Positivity is a separate property. -/
structure HermitianForm (E : Type*) [AddCommGroup E] [Module Hᵐᵒᵖ E] where
  form : E → E → H
  add_right : ∀ x y z, form x (y + z) = form x y + form x z
  mul_right : ∀ x y a, form x (rightMul y a) = form x y * a
  star_symm : ∀ x y, star (form x y) = form y x

omit [Module ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem HermitianForm.zero_right (h : HermitianForm E) (x : E) : h.form x 0 = 0 := by
  simpa [rightMul] using h.mul_right x 0 0

omit [Module ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem HermitianForm.self_eq_re (h : HermitianForm E) (x : E) :
    h.form x x = ((h.form x x).re : H) :=
  Quaternion.star_eq_self.mp (h.star_symm x x)

omit [Module ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem HermitianForm.add_left (h : HermitianForm E) (x y z : E) :
    h.form (x + y) z = h.form x z + h.form y z := by
  calc
    h.form (x + y) z = star (h.form z (x + y)) := (h.star_symm z _).symm
    _ = star (h.form z x + h.form z y) := congrArg star (h.add_right z x y)
    _ = h.form x z + h.form y z := by rw [star_add, h.star_symm, h.star_symm]

omit [Module ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem HermitianForm.mul_left (h : HermitianForm E) (x y : E) (a : H) :
    h.form (rightMul x a) y = star a * h.form x y := by
  calc
    h.form (rightMul x a) y = star (h.form y (rightMul x a)) := (h.star_symm y _).symm
    _ = star (h.form y x * a) := congrArg star (h.mul_right y x a)
    _ = star a * h.form x y := by rw [star_mul, h.star_symm]

variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)

/-- The explicit quaternionic formula from the scalar-polarisation lemma. -/
def polarForm (x y : E) : H :=
  ⟨B x y, B (rightMul x i) y, B (rightMul x j) y, B (rightMul x k) y⟩

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
/-- Coordinate reconstruction is exactly the displayed quaternionic formula
in the paper, including the signs of all imaginary coefficients. -/
theorem polarForm_eq_formula (x y : E) :
    polarForm B x y = (B x y : H) + (B (rightMul x i) y : H) * i +
      (B (rightMul x j) y : H) * j + (B (rightMul x k) y : H) * k := by
  ext <;> simp [polarForm, i, j, k]

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem polarForm_add_right (x y z : E) :
    polarForm B x (y + z) = polarForm B x y + polarForm B x z := by
  ext <;> simp [polarForm]

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem polarForm_real_smul (x y : E) (r : ℝ) :
    polarForm B x (r • y) = r • polarForm B x y := by
  ext <;> simp [polarForm]

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
/-- Orthogonality for a unit imaginary scalar gives the skew-adjoint identity.
The hypothesis will below be derived from invariance of the diagonal. -/
theorem skew_of_invariant (a : H) (ha : a * a = -1)
    (hinv : ∀ x y, B (rightMul x a) (rightMul y a) = B x y) (x y : E) :
    B (rightMul x a) y = -B x (rightMul y a) := by
  have hh := hinv (rightMul x a) y
  simpa only [rightMul_assoc, ha, rightMul_neg_one, map_neg, LinearMap.neg_apply] using hh.symm

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
/-- Polarising diagonal invariance recovers invariance of the real bilinear
form. The diagonal is not assumed to be a norm. -/
theorem invariant_of_diagonal (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x a, B (rightMul x a) (rightMul x a) =
      Quaternion.normSq a * B x x) (a : H) (ha : Quaternion.normSq a = 1) (x y : E) :
    B (rightMul x a) (rightMul y a) = B x y := by
  have hxy := hdiag (x + y) a
  have hx := hdiag x a
  have hy := hdiag y a
  simp only [ha, one_mul, rightMul_add_left, map_add, LinearMap.add_apply] at hxy hx hy
  rw [hsym (rightMul y a) (rightMul x a), hsym y x] at hxy
  linarith

variable (hi : ∀ x y, B (rightMul x i) (rightMul y i) = B x y)
variable (hj : ∀ x y, B (rightMul x j) (rightMul y j) = B x y)
variable (hk : ∀ x y, B (rightMul x k) (rightMul y k) = B x y)

include hi in
omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem polarForm_mul_i (x y : E) :
    polarForm B x (rightMul y i) = polarForm B x y * i := by
  have hsk := skew_of_invariant B i i_mul_i hi
  rw [mul_i]
  apply Quaternion.ext
  · change B x (rightMul y i) = -B (rightMul x i) y
    linarith [hsk x y]
  · exact hi x y
  · change B (rightMul x j) (rightMul y i) = B (rightMul x k) y
    have hh := hsk (rightMul x j) y
    simp only [rightMul_assoc, j_mul_i, rightMul_neg, map_neg, LinearMap.neg_apply] at hh
    linarith
  · change B (rightMul x k) (rightMul y i) = -B (rightMul x j) y
    have hh := hsk (rightMul x k) y
    simp only [rightMul_assoc, k_mul_i] at hh
    linarith

include hj in
omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem polarForm_mul_j (x y : E) :
    polarForm B x (rightMul y j) = polarForm B x y * j := by
  have hsk := skew_of_invariant B j j_mul_j hj
  rw [mul_j]
  apply Quaternion.ext
  · change B x (rightMul y j) = -B (rightMul x j) y
    linarith [hsk x y]
  · change B (rightMul x i) (rightMul y j) = -B (rightMul x k) y
    have hh := hsk (rightMul x i) y
    simp only [rightMul_assoc, i_mul_j] at hh
    linarith
  · exact hj x y
  · change B (rightMul x k) (rightMul y j) = B (rightMul x i) y
    have hh := hsk (rightMul x k) y
    simp only [rightMul_assoc, k_mul_j, rightMul_neg, map_neg, LinearMap.neg_apply] at hh
    linarith

include hk in
omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem polarForm_mul_k (x y : E) :
    polarForm B x (rightMul y k) = polarForm B x y * k := by
  have hsk := skew_of_invariant B k k_mul_k hk
  rw [mul_k]
  apply Quaternion.ext
  · change B x (rightMul y k) = -B (rightMul x k) y
    linarith [hsk x y]
  · change B (rightMul x i) (rightMul y k) = B (rightMul x j) y
    have hh := hsk (rightMul x i) y
    simp only [rightMul_assoc, i_mul_k, rightMul_neg, map_neg, LinearMap.neg_apply] at hh
    linarith
  · change B (rightMul x j) (rightMul y k) = -B (rightMul x i) y
    have hh := hsk (rightMul x j) y
    simp only [rightMul_assoc, j_mul_k] at hh
    linarith
  · exact hk x y

include hi hj hk in
theorem polarForm_mul_right (x y : E) (a : H) :
    polarForm B x (rightMul y a) = polarForm B x y * a := by
  rw [rightMul_decompose]
  simp only [polarForm_add_right, polarForm_real_smul, polarForm_mul_i B hi,
    polarForm_mul_j B hj, polarForm_mul_k B hk]
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, i, j, k] <;> ring

include hi hj hk in
omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem polarForm_star_symm (hsym : ∀ x y, B x y = B y x) (x y : E) :
    star (polarForm B x y) = polarForm B y x := by
  have hsi := skew_of_invariant B i i_mul_i hi
  have hsj := skew_of_invariant B j j_mul_j hj
  have hsk := skew_of_invariant B k k_mul_k hk
  apply Quaternion.ext <;>
    simp only [polarForm, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star]
  · exact hsym x y
  · rw [hsym (rightMul y i) x]
    linarith [hsi x y]
  · rw [hsym (rightMul y j) x]
    linarith [hsj x y]
  · rw [hsym (rightMul y k) x]
    linarith [hsk x y]

include hi hj hk in
omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
theorem polarForm_self (hsym : ∀ x y, B x y = B y x) (x : E) :
    polarForm B x x = (B x x : H) :=
  Quaternion.star_eq_self.mp (polarForm_star_symm B hi hj hk hsym x x)

/-- The actual algebraic reconstruction. Invariance of the diagonal under
quaternionic norm-squared scaling suffices; no topological assumptions occur. -/
def ofRealBilinear (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x a, B (rightMul x a) (rightMul x a) =
      Quaternion.normSq a * B x x) : HermitianForm E where
  form := polarForm B
  add_right := polarForm_add_right B
  mul_right := polarForm_mul_right B
    (invariant_of_diagonal B hsym hdiag i normSq_i)
    (invariant_of_diagonal B hsym hdiag j normSq_j)
    (invariant_of_diagonal B hsym hdiag k normSq_k)
  star_symm := polarForm_star_symm B
    (invariant_of_diagonal B hsym hdiag i normSq_i)
    (invariant_of_diagonal B hsym hdiag j normSq_j)
    (invariant_of_diagonal B hsym hdiag k normSq_k) hsym

theorem ofRealBilinear_self (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x a, B (rightMul x a) (rightMul x a) =
      Quaternion.normSq a * B x x) (x : E) :
    (ofRealBilinear B hsym hdiag).form x x = (B x x : H) :=
  polarForm_self B
    (invariant_of_diagonal B hsym hdiag i normSq_i)
    (invariant_of_diagonal B hsym hdiag j normSq_j)
    (invariant_of_diagonal B hsym hdiag k normSq_k) hsym x

/-- Strict positivity is expressed on the real diagonal; Hermitian symmetry
already makes the imaginary diagonal coefficients vanish. -/
def HermitianForm.IsPositiveDefinite (h : HermitianForm E) : Prop :=
  ∀ x : E, x ≠ 0 → 0 < (h.form x x).re

theorem ofRealBilinear_positive (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x a, B (rightMul x a) (rightMul x a) =
      Quaternion.normSq a * B x x) (hpos : ∀ x : E, x ≠ 0 → 0 < B x x) :
    (ofRealBilinear B hsym hdiag).IsPositiveDefinite := by
  intro x hx
  rw [ofRealBilinear_self, Quaternion.re_coe]
  exact hpos x hx

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
/-- A quaternionic Hermitian form with the prescribed real diagonal has the
original symmetric real bilinear form as its real part. -/
theorem HermitianForm.re_eq_realBilinear (h : HermitianForm E)
    (hsym : ∀ x y, B x y = B y x)
    (hself : ∀ x, h.form x x = (B x x : H)) (x y : E) :
    (h.form x y).re = B x y := by
  have hsum : (B (x + y) (x + y) : H) =
      h.form x x + h.form x y + (h.form y x + h.form y y) := by
    rw [← hself, h.add_left, h.add_right, h.add_right]
  have hh := congrArg QuaternionAlgebra.re hsum
  simp only [hself, Quaternion.re_add, Quaternion.re_coe] at hh
  simp only [map_add, LinearMap.add_apply] at hh
  rw [hsym y x] at hh
  have hswap : (h.form y x).re = (h.form x y).re := by
    rw [← h.star_symm x y, Quaternion.re_star]
  linarith

omit [IsScalarTower ℝ Hᵐᵒᵖ E] in
/-- Quaternionic polarisation is unique, not only a construction of some
Hermitian form with the desired diagonal. -/
theorem HermitianForm.eq_polarForm (h : HermitianForm E)
    (hsym : ∀ x y, B x y = B y x)
    (hself : ∀ x, h.form x x = (B x x : H)) (x y : E) :
    h.form x y = polarForm B x y := by
  apply Quaternion.ext
  · exact HermitianForm.re_eq_realBilinear B h hsym hself x y
  · have hh := HermitianForm.re_eq_realBilinear B h hsym hself (rightMul x i) y
    rw [h.mul_left] at hh
    simpa [Quaternion.re_mul, i] using hh
  · have hh := HermitianForm.re_eq_realBilinear B h hsym hself (rightMul x j) y
    rw [h.mul_left] at hh
    simpa [Quaternion.re_mul, j] using hh
  · have hh := HermitianForm.re_eq_realBilinear B h hsym hself (rightMul x k) y
    rw [h.mul_left] at hh
    simpa [Quaternion.re_mul, k] using hh

omit [Module ℝ E] [IsScalarTower ℝ Hᵐᵒᵖ E] in
@[ext] theorem HermitianForm.ext {h₁ h₂ : HermitianForm E}
    (hf : h₁.form = h₂.form) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hf
  rfl

/-- Existence, uniqueness and positivity of the paper's right quaternionic
Hermitian reconstruction from a positive definite real bilinear diagonal. -/
theorem existsUnique_of_realBilinear (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x a, B (rightMul x a) (rightMul x a) =
      Quaternion.normSq a * B x x) (hpos : ∀ x : E, x ≠ 0 → 0 < B x x) :
    ∃! h : HermitianForm E, (∀ x, h.form x x = (B x x : H)) ∧
      h.IsPositiveDefinite := by
  refine ⟨ofRealBilinear B hsym hdiag,
    ⟨ofRealBilinear_self B hsym hdiag, ofRealBilinear_positive B hsym hdiag hpos⟩, ?_⟩
  intro h hh
  apply HermitianForm.ext
  funext x y
  exact HermitianForm.eq_polarForm B h hsym hh.1 x y

/-- The quaternionic scalar-polarisation lemma for a genuine real quadratic
form, with norm-squared scalar homogeneity as in the paper. The right action
and original real action are both fixed in the theorem's type. -/
theorem existsUnique_of_quadraticForm (q : QuadraticForm ℝ E) (hq : q.PosDef)
    (hscale : ∀ (x : E) (a : H), q (rightMul x a) = q x * ‖a‖ ^ 2) :
    ∃! h : HermitianForm E, (∀ x, h.form x x = (q x : H)) ∧
      h.IsPositiveDefinite := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := QuadraticMap.associated q
  have hself : ∀ x : E, B x x = q x := QuadraticMap.associated_eq_self_apply ℝ q
  have hsym : ∀ x y : E, B x y = B y x := QuadraticMap.associated_isSymm ℝ q
  have hdiag : ∀ (x : E) (a : H), B (rightMul x a) (rightMul x a) =
      Quaternion.normSq a * B x x := by
    intro x a
    rw [hself, hself, Quaternion.normSq_eq_norm_mul_self, hscale]
    ring
  have hpos : ∀ x : E, x ≠ 0 → 0 < B x x := by
    intro x hx
    rw [hself]
    exact hq x hx
  obtain ⟨h, hh, huniq⟩ := existsUnique_of_realBilinear B hsym hdiag hpos
  refine ⟨h, ⟨?_, hh.2⟩, ?_⟩
  · intro x
    rw [hh.1, hself]
  · intro h' hh'
    apply huniq h'
    refine ⟨?_, hh'.2⟩
    intro x
    rw [hh'.1, hself]

end Quaternionic
end BanachIsometric
