import NonCalkinAlgebra.TwistedAveraging

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
universe u
variable {G : Type u} [AddCommGroup G]

@[simp] theorem star_shiftInAlgebra_mul_self (c : Cocycle G) (g : G) :
    star (shiftInAlgebra c g) * shiftInAlgebra c g = 1 :=
  Subtype.ext (star_shift_mul_self c g)

theorem conjugateShift_eq_self_iff (c : Cocycle G) (g : G) (a : closedSubalgebra c) :
    conjugateShift c g a = a ↔ shiftInAlgebra c g * a = a * shiftInAlgebra c g := by
  constructor
  · intro ha
    have hm := congrArg (fun b : closedSubalgebra c => b * shiftInAlgebra c g) ha
    simpa only [conjugateShift_apply, mul_assoc, star_shiftInAlgebra_mul_self, mul_one] using hm
  · intro ha
    rw [conjugateShift_apply, ha, mul_assoc, shiftInAlgebra_mul_star_self, mul_one]

end NonCalkinAlgebra.TwistedRegular
