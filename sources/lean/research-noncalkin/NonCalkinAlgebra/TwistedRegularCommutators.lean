import NonCalkinAlgebra.TwistedRegular
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
open BinaryPhase
universe u
variable {G : Type u} [AddCommGroup G]

theorem shift_commutes_of_symmetric (c : Cocycle G) (g k : G)
    (hc : c g k = c k g) : shift c g * shift c k = shift c k * shift c g := by
  rw [shift_mul, shift_mul, hc, add_comm g k]

theorem shift_anticommutes_of_values (c : Cocycle G) (g k : G)
    (h1 : c g k = 1) (h0 : c k g = 0) :
    shift c g * shift c k = -(shift c k * shift c g) := by
  rw [shift_mul, shift_mul, h1, h0, phase_one, phase_zero,
    one_smul, neg_one_smul, add_comm g k]

theorem commutator_value_eq_zero (c : Cocycle G) (g k : G)
    (h0 : c g k = 0) (h0' : c k g = 0) :
    (1 / 2 : ℝ) * ‖shift c g * shift c k - shift c k * shift c g‖ = 0 := by
  rw [shift_commutes_of_symmetric c g k (h0.trans h0'.symm), sub_self, norm_zero, mul_zero]

theorem commutator_value_eq_one (c : Cocycle G) (g k : G)
    (h1 : c g k = 1) (h0 : c k g = 0) :
    (1 / 2 : ℝ) * ‖shift c g * shift c k - shift c k * shift c g‖ = 1 := by
  have hanti := shift_anticommutes_of_values c g k h1 h0
  have hrev : shift c k * shift c g = -(shift c g * shift c k) := by
    simpa only [neg_neg] using (congrArg Neg.neg hanti).symm
  have hdiff : shift c g * shift c k - shift c k * shift c g =
      (2 : ℂ) • (shift c g * shift c k) := by
    rw [hrev, sub_neg_eq_add, two_smul]
  rw [hdiff, norm_smul, norm_shift_mul]
  norm_num

end NonCalkinAlgebra.TwistedRegular
