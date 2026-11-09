import NonCalkinAlgebra.TwistedRightRegular

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
open scoped InnerProductSpace
universe u
variable {G : Type u} [AddCommGroup G]

def coefficientLinear (c : Cocycle G) : closedSubalgebra c →ₗ[ℂ] ℂ where
  toFun a := inner ℂ (delta 0) ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0))
  map_add' a b := by
    change inner ℂ (delta 0) ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0) +
      (b : SquareSummable G →L[ℂ] SquareSummable G) (delta 0)) = _
    exact inner_add_right _ _ _
  map_smul' z a := by
    change inner ℂ (delta 0) (z • ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0))) = _
    rw [inner_smul_right]
    rfl

theorem coefficientLinear_bound (c : Cocycle G) (a : closedSubalgebra c) :
    ‖coefficientLinear c a‖ ≤ ‖a‖ := by
  calc
    ‖coefficientLinear c a‖ ≤ ‖delta (0 : G)‖ *
        ‖(a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0)‖ :=
      norm_inner_le_norm (𝕜 := ℂ) (delta 0)
        ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0))
    _ = ‖(a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0)‖ := by rw [norm_delta, one_mul]
    _ ≤ ‖(a : SquareSummable G →L[ℂ] SquareSummable G)‖ * ‖delta (0 : G)‖ :=
      (a : SquareSummable G →L[ℂ] SquareSummable G).le_opNorm _
    _ = ‖a‖ := by rw [norm_delta, mul_one]; rfl

/-- The bounded canonical coefficient functional of the concrete algebra. -/
def coefficientZero (c : Cocycle G) : closedSubalgebra c →L[ℂ] ℂ :=
  (coefficientLinear c).mkContinuous 1 (fun a => by
    simpa only [one_mul] using coefficientLinear_bound c a)

@[simp] theorem coefficientZero_apply (c : Cocycle G) (a : closedSubalgebra c) :
    coefficientZero c a = inner ℂ (delta 0)
      ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0)) := rfl

theorem norm_coefficientZero_le (c : Cocycle G) (a : closedSubalgebra c) :
    ‖coefficientZero c a‖ ≤ ‖a‖ := coefficientLinear_bound c a

@[simp] theorem coefficientZero_one (c : Cocycle G) : coefficientZero c 1 = 1 := by
  classical
  simp [coefficientZero_apply, delta, lp.inner_single_left, lp.coeFn_single]

@[simp] theorem coefficientZero_shift_zero (c : Cocycle G) :
    coefficientZero c (shiftInAlgebra c 0) = 1 := by rw [shiftInAlgebra_zero, coefficientZero_one]

theorem coefficientZero_shift_of_ne_zero (c : Cocycle G) (g : G) (hg : g ≠ 0) :
    coefficientZero c (shiftInAlgebra c g) = 0 := by
  classical
  change inner ℂ (delta 0) (shift c g (delta 0)) = 0
  rw [shift_delta_zero]
  simp [delta, lp.inner_single_left, lp.coeFn_single, Ne.symm hg]

theorem coefficientZero_star_mul_self (c : Cocycle G) (a : closedSubalgebra c) :
    coefficientZero c (star a * a) = inner ℂ
      ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0))
      ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0)) := by
  change inner ℂ (delta 0)
    (ContinuousLinearMap.adjoint (a : SquareSummable G →L[ℂ] SquareSummable G)
      ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0))) = _
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

/-- Faithfulness at a*a; no false claim that the coefficient of every
nonzero algebra element is nonzero is made. -/
theorem coefficientZero_star_mul_self_eq_zero_iff (c : Cocycle G) (a : closedSubalgebra c) :
    coefficientZero c (star a * a) = 0 ↔ a = 0 := by
  rw [coefficientZero_star_mul_self, inner_self_eq_zero]
  constructor
  · exact eq_zero_of_apply_delta_zero c a
  · intro h
    subst a
    rfl

end NonCalkinAlgebra.TwistedRegular
