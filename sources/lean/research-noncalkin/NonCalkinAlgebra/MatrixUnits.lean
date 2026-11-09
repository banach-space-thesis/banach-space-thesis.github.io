import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Mul

/-! The actual `D`-valued coordinate operators of Section 5 of the paper.
The underlying space is mathlib's Banach ℓ¹ space, not finitely supported
vectors or a space carrying a custom replacement norm.
-/

noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators

namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]

abbrev CoefficientSpace := lp (fun _ : ℕ => D) 1

def coordinate (j : ℕ) : CoefficientSpace D →L[ℂ] D :=
  (show CoefficientSpace D →ₗ[ℂ] D from
    { toFun := fun x => x j
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }).mkContinuous 1
      (fun x => by simpa only [one_mul] using lp.norm_apply_le_norm one_ne_zero x j)

@[simp] theorem coordinate_apply (j : ℕ) (x : CoefficientSpace D) :
    coordinate D j x = x j := rfl

def theta (i j : ℕ) (d : D) : CoefficientSpace D →L[ℂ] CoefficientSpace D :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => D) 1 i).comp
    ((ContinuousLinearMap.mul ℂ D d).comp (coordinate D j))

@[simp] theorem theta_apply (i j : ℕ) (d : D) (x : CoefficientSpace D) :
    theta D i j d x = lp.single 1 i (d * x j) := rfl

theorem norm_theta_le (i j : ℕ) (d : D) : ‖theta D i j d‖ ≤ ‖d‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg d)
  intro x
  rw [theta_apply, lp.norm_single zero_lt_one]
  exact (norm_mul_le d (x j)).trans
    (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm one_ne_zero x j) (norm_nonneg d))

theorem theta_mul (i j k l : ℕ) (d e : D) :
    theta D i j d * theta D k l e = if j = k then theta D i l (d * e) else 0 := by
  classical
  by_cases hjk : j = k
  · subst k
    ext x n
    simp [ContinuousLinearMap.mul_apply, theta_apply, lp.single_apply, mul_assoc]
  · simp only [if_neg hjk]
    ext x n
    simp [ContinuousLinearMap.mul_apply, theta_apply, lp.single_apply, hjk]

theorem theta_add (i j : ℕ) (d e : D) :
    theta D i j (d + e) = theta D i j d + theta D i j e := by
  ext x n
  simp [theta_apply, lp.single_apply, add_mul]

theorem theta_smul (i j : ℕ) (a : ℂ) (d : D) :
    theta D i j (a • d) = a • theta D i j d := by
  ext x n
  simp [theta_apply, lp.single_apply]

variable [NormOneClass D]

/-- Equation (10): the coefficient map is isometric in the actual operator norm. -/
theorem norm_theta (i j : ℕ) (d : D) : ‖theta D i j d‖ = ‖d‖ := by
  apply le_antisymm (norm_theta_le D i j d)
  have h := (theta D i j d).le_opNorm (lp.single 1 j (1 : D))
  simpa only [theta_apply, lp.single_apply_self, mul_one, lp.norm_single zero_lt_one,
    norm_one, mul_one] using h

def scalarMatrixUnit (i j : ℕ) : CoefficientSpace D →L[ℂ] CoefficientSpace D :=
  theta D i j 1

@[simp] theorem norm_scalarMatrixUnit (i j : ℕ) : ‖scalarMatrixUnit D i j‖ = 1 := by
  simp [scalarMatrixUnit, norm_theta]

omit [NormOneClass D] in
theorem scalarMatrixUnit_mul (i j k l : ℕ) :
    scalarMatrixUnit D i j * scalarMatrixUnit D k l =
      if j = k then scalarMatrixUnit D i l else 0 := by
  simpa only [scalarMatrixUnit, one_mul] using theta_mul D i j k l 1 1

omit [NormOneClass D] in
theorem scalarMatrixUnit_ne_zero [Nontrivial D] (i j : ℕ) : scalarMatrixUnit D i j ≠ 0 := by
  intro h
  have hvalue := congrArg
    (fun T : CoefficientSpace D →L[ℂ] CoefficientSpace D =>
      T (lp.single 1 j (1 : D)) i) h
  have hzero : (1 : D) = 0 := by
    simpa [scalarMatrixUnit, theta_apply, lp.single_apply] using hvalue
  exact one_ne_zero hzero

end NonCalkinAlgebra
