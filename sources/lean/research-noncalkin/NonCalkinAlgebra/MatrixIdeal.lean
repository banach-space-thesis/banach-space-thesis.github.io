import NonCalkinAlgebra.UnitizedMatrixAlgebra
import NonCalkinAlgebra.OneIdealCriterion

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]

theorem matrixClosure_mul_left {a j : CoefficientSpace D →L[ℂ] CoefficientSpace D}
    (ha : a ∈ matrixAlgebra D) (hj : j ∈ matrixClosure D) :
    a * j ∈ matrixClosure D := by
  obtain ⟨c, k, hk, rfl⟩ := (mem_unitizedMatrixSubspace D a).mp ha
  simpa only [add_mul, smul_mul_assoc, one_mul] using
    (matrixClosure D).add_mem ((matrixClosure D).smul_mem c hj) (matrixClosure_mul D hk hj)

theorem matrixClosure_mul_right {a j : CoefficientSpace D →L[ℂ] CoefficientSpace D}
    (ha : a ∈ matrixAlgebra D) (hj : j ∈ matrixClosure D) :
    j * a ∈ matrixClosure D := by
  obtain ⟨c, k, hk, rfl⟩ := (mem_unitizedMatrixSubspace D a).mp ha
  simpa only [mul_add, mul_smul_comm, mul_one] using
    (matrixClosure D).add_mem ((matrixClosure D).smul_mem c hj) (matrixClosure_mul D hj hk)

/-- The actual closed matrix ideal, regarded as an ideal of A_D. -/
def matrixIdeal : TwoSidedIdeal (matrixAlgebra D) :=
  TwoSidedIdeal.mk' {a | (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) ∈ matrixClosure D}
    (matrixClosure D).zero_mem
    (fun ha hb => (matrixClosure D).add_mem ha hb)
    (fun ha => (matrixClosure D).neg_mem ha)
    (fun {a j} hj => matrixClosure_mul_left D a.property hj)
    (fun {j a} hj => matrixClosure_mul_right D a.property hj)

@[simp] theorem mem_matrixIdeal (a : matrixAlgebra D) :
    a ∈ matrixIdeal D ↔
      (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) ∈ matrixClosure D := by
  simp only [matrixIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

theorem matrixIdeal_isClosed : IsClosed (matrixIdeal D : Set (matrixAlgebra D)) := by
  have h := (matrixClosure_isClosed D).preimage
    (continuous_subtype_val : Continuous (fun a : matrixAlgebra D =>
      (a : CoefficientSpace D →L[ℂ] CoefficientSpace D)))
  simpa only [matrixIdeal, TwoSidedIdeal.coe_mk'] using h

def matrixTheta (i j : ℕ) (d : D) : matrixAlgebra D :=
  ⟨theta D i j d, theta_mem_matrixAlgebra D i j d⟩

@[simp] theorem coe_matrixTheta (i j : ℕ) (d : D) :
    (matrixTheta D i j d : CoefficientSpace D →L[ℂ] CoefficientSpace D) = theta D i j d := rfl

theorem matrixTheta_mem_matrixIdeal (i j : ℕ) (d : D) :
    matrixTheta D i j d ∈ matrixIdeal D :=
  (mem_matrixIdeal D _).mpr (theta_mem_matrixClosure D i j d)

variable [NormOneClass D]

theorem matrixIdeal_ne_top : matrixIdeal D ≠ ⊤ := by
  intro h
  have hone := (matrixIdeal D).one_mem h
  exact one_not_mem_matrixClosure D ((mem_matrixIdeal D 1).mp hone)

theorem matrixIdeal_ne_bot : matrixIdeal D ≠ ⊥ := by
  intro h
  have he := matrixTheta_mem_matrixIdeal D 0 0 1
  rw [h, TwoSidedIdeal.mem_bot] at he
  have hzero : theta D 0 0 1 = 0 := congrArg Subtype.val he
  have hnorm := norm_theta D 0 0 (1 : D)
  have hnormZero : ‖(0 : CoefficientSpace D →L[ℂ] CoefficientSpace D)‖ = 0 :=
    norm_zero (E := CoefficientSpace D →L[ℂ] CoefficientSpace D)
  have hnormOne : ‖(1 : D)‖ = 1 := norm_one
  rw [hzero, hnormZero, hnormOne] at hnorm
  exact zero_ne_one hnorm

theorem matrixIdeal_isNonzeroProperClosed :
    IsNonzeroProperClosedIdeal (A := matrixAlgebra D) (matrixIdeal D) :=
  ⟨matrixIdeal_isClosed D, matrixIdeal_ne_bot D, matrixIdeal_ne_top D⟩

theorem matrixIdeal_has_no_identity :
    ¬ ∃ U ∈ matrixIdeal D, ∀ a ∈ matrixIdeal D, U * a = a ∧ a * U = a := by
  rintro ⟨U, hU, hunit⟩
  apply matrixClosure_has_no_identity D
  refine ⟨U, (mem_matrixIdeal D U).mp hU, ?_⟩
  intro T hT
  let a : matrixAlgebra D := ⟨T, matrixClosure_mem_matrixAlgebra D hT⟩
  have ha : a ∈ matrixIdeal D := (mem_matrixIdeal D a).mpr hT
  have h := hunit a ha
  exact ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩

end NonCalkinAlgebra
