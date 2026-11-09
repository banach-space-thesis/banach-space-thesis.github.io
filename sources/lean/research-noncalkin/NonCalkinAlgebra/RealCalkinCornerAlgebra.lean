import NonCalkinAlgebra.ComplexificationQuotientCoordinates
import NonCalkinAlgebra.RealQuotientIsoEquiv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.RealCalkinCorner
open BanachComplexification
universe u v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (k : QuotientConvention) {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
  (e : RealOperatorQuotientIso X k A)

abbrev B := OperatorQuotient (BanachComplexification X) k

def H : A →L[ℝ] B X k := (quotientMap X k).comp e.toContinuousLinearEquiv.symm.toContinuousLinearMap

@[simp] theorem H_apply (a : A) : H X k e a = quotientMap X k (e.toContinuousLinearEquiv.symm a) := rfl

theorem H_mul (a b : A) : H X k e (a * b) = H X k e a * H X k e b := by
  have h := _root_.map_mul e.toContinuousAlgEquiv.symm a b
  change e.toContinuousLinearEquiv.symm (a * b) =
    e.toContinuousLinearEquiv.symm a * e.toContinuousLinearEquiv.symm b at h
  rw [H_apply, H_apply, H_apply, h, quotientMap_mul]

theorem H_one : H X k e 1 = 1 := by
  have h := _root_.map_one e.toContinuousAlgEquiv.symm
  change e.toContinuousLinearEquiv.symm 1 = 1 at h
  rw [H_apply, h, quotientMap_one]

def j : B X k := H X k e (Complex.I • (1 : A))

theorem j_sq : j X k e * j X k e = -1 := by
  change H X k e (Complex.I • (1 : A)) * H X k e (Complex.I • (1 : A)) = _
  rw [← H_mul, smul_mul_assoc, mul_smul_comm, one_mul, smul_smul,
    Complex.I_mul_I, neg_one_smul, map_neg, H_one]

theorem H_I (a : A) : H X k e (Complex.I • a) = j X k e * H X k e a := by
  change H X k e (Complex.I • a) = H X k e (Complex.I • (1 : A)) * H X k e a
  rw [← H_mul, smul_mul_assoc, one_mul]

theorem j_comm_H (a : A) : j X k e * H X k e a = H X k e a * j X k e := by
  change H X k e (Complex.I • (1 : A)) * H X k e a =
    H X k e a * H X k e (Complex.I • (1 : A))
  rw [← H_mul, ← H_mul, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem H_decomposition (b : B X k) :
    b = H X k e (e.toContinuousLinearEquiv (quotientRealPart X k b)) -
      Complex.I • H X k e (e.toContinuousLinearEquiv (quotientImagCoordinate X k b)) := by
  simpa only [H_apply, ContinuousLinearEquiv.symm_apply_apply] using quotient_decomposition X k b

theorem j_comm (b : B X k) : j X k e * b = b * j X k e := by
  calc
    j X k e * b = j X k e *
        (H X k e (e.toContinuousLinearEquiv (quotientRealPart X k b)) -
          Complex.I • H X k e (e.toContinuousLinearEquiv (quotientImagCoordinate X k b))) :=
      congrArg (j X k e * ·) (H_decomposition X k e b)
    _ = (H X k e (e.toContinuousLinearEquiv (quotientRealPart X k b)) -
          Complex.I • H X k e (e.toContinuousLinearEquiv (quotientImagCoordinate X k b))) * j X k e := by
      rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, j_comm_H, j_comm_H]
    _ = b * j X k e := congrArg (· * j X k e) (H_decomposition X k e b).symm

/-- The central idempotent (1-ij)/2, expanded as a linear combination. -/
def p : B X k := (1 / 2 : ℂ) • (1 : B X k) - ((1 / 2 : ℂ) * Complex.I) • j X k e

theorem p_j : p X k e * j X k e = Complex.I • p X k e := by
  have hc : Complex.I * ((1 / 2 : ℂ) * Complex.I) = -(1 / 2 : ℂ) := by
    calc
      Complex.I * ((1 / 2 : ℂ) * Complex.I) = (1 / 2 : ℂ) * (Complex.I * Complex.I) := by ring
      _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I, mul_neg_one]
  change ((1 / 2 : ℂ) • (1 : B X k) - ((1 / 2 : ℂ) * Complex.I) • j X k e) * j X k e =
    Complex.I • ((1 / 2 : ℂ) • (1 : B X k) - ((1 / 2 : ℂ) * Complex.I) • j X k e)
  rw [sub_mul, smul_mul_assoc, one_mul, smul_mul_assoc, j_sq, smul_neg, sub_neg_eq_add,
    smul_sub, smul_smul, smul_smul, hc, neg_smul, sub_neg_eq_add]
  rw [mul_comm Complex.I (1 / 2 : ℂ)]
  exact add_comm _ _

theorem p_sq : p X k e * p X k e = p X k e := by
  have hc : ((1 / 2 : ℂ) * Complex.I) * Complex.I = -(1 / 2 : ℂ) := by
    rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
  change p X k e * ((1 / 2 : ℂ) • (1 : B X k) -
    ((1 / 2 : ℂ) * Complex.I) • j X k e) = p X k e
  rw [mul_sub, mul_smul_comm, mul_one, mul_smul_comm, p_j, smul_smul, hc,
    neg_smul, sub_neg_eq_add, ← add_smul]
  norm_num

theorem p_comm (b : B X k) : p X k e * b = b * p X k e := by
  change ((1 / 2 : ℂ) • (1 : B X k) - ((1 / 2 : ℂ) * Complex.I) • j X k e) * b =
    b * ((1 / 2 : ℂ) • (1 : B X k) - ((1 / 2 : ℂ) * Complex.I) • j X k e)
  rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, smul_mul_assoc,
    mul_smul_comm, mul_one, mul_smul_comm, j_comm]

end NonCalkinAlgebra.RealCalkinCorner
