import NonCalkinAlgebra.TwistedFiniteSpan
import Mathlib.Analysis.Normed.Operator.Mul

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
open BinaryPhase
universe u v
variable {G : Type u} [AddCommGroup G]

@[simp] theorem shiftInAlgebra_mul_star_self (c : Cocycle G) (g : G) :
    shiftInAlgebra c g * star (shiftInAlgebra c g) = 1 :=
  Subtype.ext (shift_mul_star_self c g)

def conjugateShift (c : Cocycle G) (h : G) : closedSubalgebra c →L[ℂ] closedSubalgebra c :=
  ContinuousLinearMap.mulLeftRight ℂ (closedSubalgebra c)
    (shiftInAlgebra c h) (star (shiftInAlgebra c h))

@[simp] theorem conjugateShift_apply (c : Cocycle G) (h : G) (a : closedSubalgebra c) :
    conjugateShift c h a = shiftInAlgebra c h * a * star (shiftInAlgebra c h) := rfl

theorem conjugateShift_shift (c : Cocycle G) (h g : G) :
    conjugateShift c h (shiftInAlgebra c g) =
      phase (c h g + c g h) • shiftInAlgebra c g := by
  have hc : shiftInAlgebra c h * shiftInAlgebra c g =
      phase (c h g + c g h) • (shiftInAlgebra c g * shiftInAlgebra c h) :=
    Subtype.ext (shift_commutation c h g)
  rw [conjugateShift_apply, hc, smul_mul_assoc, mul_assoc,
    shiftInAlgebra_mul_star_self, mul_one]

theorem norm_conjugateShift_le (c : Cocycle G) (h : G) (a : closedSubalgebra c) :
    ‖conjugateShift c h a‖ ≤ ‖a‖ := by
  calc
    _ ≤ (‖shiftInAlgebra c h‖ * ‖a‖) * ‖star (shiftInAlgebra c h)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖a‖ := by rw [norm_star, norm_shiftInAlgebra, one_mul, mul_one]

def halfSumMap {A : Type v} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (T : A →L[ℂ] A) : A →L[ℂ] A :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ A + T)

def averageShift (c : Cocycle G) (h : G) : closedSubalgebra c →L[ℂ] closedSubalgebra c :=
  halfSumMap (conjugateShift c h)

@[simp] theorem averageShift_apply (c : Cocycle G) (h : G) (a : closedSubalgebra c) :
    averageShift c h a = (1 / 2 : ℂ) • (a + conjugateShift c h a) := rfl

@[simp] theorem averageShift_one (c : Cocycle G) (h : G) : averageShift c h 1 = 1 := by
  rw [averageShift_apply, conjugateShift_apply, mul_one, shiftInAlgebra_mul_star_self]
  conv_lhs => rw [← one_smul ℂ (1 : closedSubalgebra c), ← add_smul, smul_smul]
  norm_num

theorem norm_averageShift_le (c : Cocycle G) (h : G) (a : closedSubalgebra c) :
    ‖averageShift c h a‖ ≤ ‖a‖ := by
  rw [averageShift_apply, norm_smul]
  have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
  rw [hn]
  calc
    (1 / 2 : ℝ) * ‖a + conjugateShift c h a‖ ≤
        (1 / 2 : ℝ) * (‖a‖ + ‖conjugateShift c h a‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (‖a‖ + ‖a‖) :=
      mul_le_mul_of_nonneg_left (add_le_add_left (norm_conjugateShift_le c h a) _) (by norm_num)
    _ = ‖a‖ := by ring

theorem averageShift_mem (c : Cocycle G) (h : G) (I : TwoSidedIdeal (closedSubalgebra c))
    {a : closedSubalgebra c} (ha : a ∈ I) : averageShift c h a ∈ I := by
  rw [averageShift_apply, conjugateShift_apply]
  exact twoSidedIdeal_smul_mem I (I.add_mem ha
    (I.mul_mem_right _ _ (I.mul_mem_left _ _ ha))) _

theorem averageShift_shift_of_zero (c : Cocycle G) (h g : G)
    (hb : c h g + c g h = 0) : averageShift c h (shiftInAlgebra c g) = shiftInAlgebra c g := by
  rw [averageShift_apply, conjugateShift_shift, hb, phase_zero, one_smul]
  conv_lhs => rw [← one_smul ℂ (shiftInAlgebra c g), ← add_smul, smul_smul]
  norm_num

theorem averageShift_shift_of_ne_zero (c : Cocycle G) (h g : G)
    (hb : c h g + c g h ≠ 0) : averageShift c h (shiftInAlgebra c g) = 0 := by
  rw [averageShift_apply, conjugateShift_shift]
  simp [phase, hb]

theorem averageShift_shift_eq_zero_or_self (c : Cocycle G) (h g : G) :
    averageShift c h (shiftInAlgebra c g) = 0 ∨
      averageShift c h (shiftInAlgebra c g) = shiftInAlgebra c g := by
  by_cases hb : c h g + c g h = 0
  · exact Or.inr (averageShift_shift_of_zero c h g hb)
  · exact Or.inl (averageShift_shift_of_ne_zero c h g hb)

end NonCalkinAlgebra.TwistedRegular
