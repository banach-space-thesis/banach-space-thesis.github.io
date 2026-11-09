import SurveyStatements.P2OppositeShift

/-! Actual quotient representatives and transported bounded-row matrix units. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]

def boundedCalkinLift (s : Calkin X) : BoundedOperators X :=
  Classical.choose (Submodule.Quotient.norm_mk_lt s zero_lt_one)

@[simp] theorem calkinQuotient_boundedCalkinLift (s : Calkin X) :
    calkinQuotient X (boundedCalkinLift X s) = s :=
  (Classical.choose_spec (Submodule.Quotient.norm_mk_lt s zero_lt_one)).1

theorem norm_boundedCalkinLift_lt (s : Calkin X) : ‖boundedCalkinLift X s‖ < ‖s‖ + 1 :=
  (Classical.choose_spec (Submodule.Quotient.norm_mk_lt s zero_lt_one)).2

variable [CompleteSpace X]

def transportedMatrixUnit
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)ᵐᵒᵖ) (i j : ℕ) : Calkin X :=
  e.toContinuousLinearEquiv.symm (countableOppositeMatrixUnit i j)

theorem transportedMatrixUnit_mul
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)ᵐᵒᵖ) (i j k l : ℕ) :
    transportedMatrixUnit X e i j * transportedMatrixUnit X e k l =
      if j = k then transportedMatrixUnit X e i l else 0 := by
  classical
  change (CalkinBanachAlgebraIso.toAlgEquiv X e).symm (countableOppositeMatrixUnit i j) *
      (CalkinBanachAlgebraIso.toAlgEquiv X e).symm (countableOppositeMatrixUnit k l) = _
  rw [← map_mul, countableOppositeMatrixUnit_mul]
  split_ifs <;> simp [transportedMatrixUnit, CalkinBanachAlgebraIso.toAlgEquiv]

theorem transportedMatrixUnit_diagonal_ne_zero
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)ᵐᵒᵖ) (i : ℕ) :
    transportedMatrixUnit X e i i ≠ 0 := by
  intro h
  have hz := e.toContinuousLinearEquiv.symm.injective
    (h.trans e.toContinuousLinearEquiv.symm.map_zero.symm)
  exact countableOppositeMatrixUnit_diagonal_ne_zero i hz

theorem norm_transportedMatrixUnit_le
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)ᵐᵒᵖ) (i j : ℕ) :
    ‖transportedMatrixUnit X e i j‖ ≤ ‖e.toContinuousLinearEquiv.symm.toContinuousLinearMap‖ := by
  exact (e.toContinuousLinearEquiv.symm.toContinuousLinearMap.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_countableOppositeMatrixUnit_le i j)
      (norm_nonneg _)).trans_eq (mul_one _))

theorem norm_sum_transportedMatrixUnit_row_le
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)ᵐᵒᵖ)
    (i : ℕ) (F : Finset ℕ) (z : ℕ → ℂ) (hz : ∀ j ∈ F, ‖z j‖ ≤ 1) :
    ‖∑ j ∈ F, z j • transportedMatrixUnit X e i j‖ ≤
      ‖e.toContinuousLinearEquiv.symm.toContinuousLinearMap‖ := by
  have hsum : ∑ j ∈ F, z j • transportedMatrixUnit X e i j =
      e.toContinuousLinearEquiv.symm (∑ j ∈ F, z j • countableOppositeMatrixUnit i j) := by
    simp only [transportedMatrixUnit, map_sum, map_smul]
  rw [hsum]
  exact (e.toContinuousLinearEquiv.symm.toContinuousLinearMap.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left
      (norm_sum_countableOppositeMatrixUnit_row_le i F z 1 zero_le_one hz)
      (norm_nonneg _)).trans_eq (mul_one _))

theorem norm_sum_transportedMatrixUnit_row_le_mul
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)ᵐᵒᵖ)
    (i : ℕ) (F : Finset ℕ) (z : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ j ∈ F, ‖z j‖ ≤ C) :
    ‖∑ j ∈ F, z j • transportedMatrixUnit X e i j‖ ≤
      ‖e.toContinuousLinearEquiv.symm.toContinuousLinearMap‖ * C := by
  have hsum : ∑ j ∈ F, z j • transportedMatrixUnit X e i j =
      e.toContinuousLinearEquiv.symm (∑ j ∈ F, z j • countableOppositeMatrixUnit i j) := by
    simp only [transportedMatrixUnit, map_sum, map_smul]
  rw [hsum]
  exact (e.toContinuousLinearEquiv.symm.toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left
      (norm_sum_countableOppositeMatrixUnit_row_le i F z C hC hz) (norm_nonneg _))

theorem norm_sum_transportedMatrixUnit_finite_row_le
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)ᵐᵒᵖ)
    (i : ℕ) (F : Finset ℕ) (a : F → ℂ) :
    ‖∑ j : F, a j • transportedMatrixUnit X e i j.val‖ ≤
      ‖e.toContinuousLinearEquiv.symm.toContinuousLinearMap‖ * ‖a‖ := by
  classical
  let z : ℕ → ℂ := fun j => if h : j ∈ F then a ⟨j, h⟩ else 0
  have hz : ∀ j ∈ F, ‖z j‖ ≤ ‖a‖ := by
    intro j hj
    simpa only [z, dif_pos hj] using norm_le_pi_norm a ⟨j, hj⟩
  have h := norm_sum_transportedMatrixUnit_row_le_mul X e i F z ‖a‖ (norm_nonneg _) hz
  rw [← Finset.sum_coe_sort] at h
  have hcoeff (j : F) : z j.val = a j := by
    simp only [z, dif_pos j.property]
  simpa only [hcoeff] using h

end SurveyStatements.P2
