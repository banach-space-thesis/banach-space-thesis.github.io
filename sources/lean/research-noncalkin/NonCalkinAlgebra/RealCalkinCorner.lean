import NonCalkinAlgebra.RealCalkinCornerAlgebra
import NonCalkinAlgebra.ComplexLinearOfReal
import NonCalkinAlgebra.CornerModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.RealCalkinCorner
open BanachComplexification
universe u v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (k : QuotientConvention) {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
  (e : RealOperatorQuotientIso X k A)

def projectionReal : B X k →L[ℝ] A :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp (quotientRealPart X k) -
    ((Complex.I • ContinuousLinearMap.id ℂ A).restrictScalars ℝ).comp
      (e.toContinuousLinearEquiv.toContinuousLinearMap.comp (quotientImagCoordinate X k))

@[simp] theorem projectionReal_apply (b : B X k) :
    projectionReal X k e b = e.toContinuousLinearEquiv (quotientRealPart X k b) -
      Complex.I • e.toContinuousLinearEquiv (quotientImagCoordinate X k b) := rfl

theorem projectionReal_I (b : B X k) :
    projectionReal X k e (Complex.I • b) = Complex.I • projectionReal X k e b := by
  rw [projectionReal_apply, projectionReal_apply, quotientRealPart_I_smul,
    quotientImagCoordinate_I_smul, map_neg, smul_neg, sub_neg_eq_add,
    smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add]
  exact add_comm _ _

def projection : B X k →L[ℂ] A :=
  complexLinearOfReal (projectionReal X k e) (projectionReal_I X k e)

@[simp] theorem projection_apply (b : B X k) :
    projection X k e b = e.toContinuousLinearEquiv (quotientRealPart X k b) -
      Complex.I • e.toContinuousLinearEquiv (quotientImagCoordinate X k b) := rfl

theorem projection_H (a : A) : projection X k e (H X k e a) = a := by
  rw [projection_apply, H_apply, quotientRealPart_map, quotientImagCoordinate_map,
    map_zero, smul_zero, sub_zero, ContinuousLinearEquiv.apply_symm_apply]

def inclusionReal : A →L[ℝ] B X k :=
  ((ContinuousLinearMap.mul ℂ (B X k) (p X k e)).restrictScalars ℝ).comp (H X k e)

@[simp] theorem inclusionReal_apply (a : A) : inclusionReal X k e a = p X k e * H X k e a := rfl

theorem inclusionReal_I (a : A) :
    inclusionReal X k e (Complex.I • a) = Complex.I • inclusionReal X k e a := by
  rw [inclusionReal_apply, inclusionReal_apply, H_I, ← mul_assoc, p_j, smul_mul_assoc]

def inclusion : A →L[ℂ] B X k :=
  complexLinearOfReal (inclusionReal X k e) (inclusionReal_I X k e)

@[simp] theorem inclusion_apply (a : A) : inclusion X k e a = p X k e * H X k e a := rfl

theorem inclusion_one : inclusion X k e 1 = p X k e := by rw [inclusion_apply, H_one, mul_one]

theorem inclusion_mul (a b : A) :
    inclusion X k e (a * b) = inclusion X k e a * inclusion X k e b := by
  rw [inclusion_apply, inclusion_apply, inclusion_apply, H_mul]
  symm
  calc
    (p X k e * H X k e a) * (p X k e * H X k e b) =
        (p X k e * (H X k e a * p X k e)) * H X k e b := by simp only [mul_assoc]
    _ = (p X k e * (p X k e * H X k e a)) * H X k e b := by rw [← p_comm]
    _ = (p X k e * p X k e) * (H X k e a * H X k e b) := by simp only [mul_assoc]
    _ = p X k e * (H X k e a * H X k e b) := by rw [p_sq]

theorem inclusion_expansion (a : A) :
    inclusion X k e a = (1 / 2 : ℂ) • H X k e a -
      ((1 / 2 : ℂ) * Complex.I) • H X k e (Complex.I • a) := by
  change ((1 / 2 : ℂ) • (1 : B X k) - ((1 / 2 : ℂ) * Complex.I) • j X k e) * H X k e a = _
  rw [sub_mul, smul_mul_assoc, one_mul, smul_mul_assoc, ← H_I]

theorem projection_inclusion (a : A) : projection X k e (inclusion X k e a) = a := by
  have hc : ((1 / 2 : ℂ) * Complex.I) * Complex.I = -(1 / 2 : ℂ) := by
    rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
  rw [inclusion_expansion, map_sub, map_smul, map_smul, projection_H, projection_H,
    smul_smul, hc, neg_smul, sub_neg_eq_add, ← add_smul]
  norm_num

theorem inclusion_projection (b : B X k) :
    inclusion X k e (projection X k e b) = p X k e * b * p X k e := by
  calc
    inclusion X k e (projection X k e b) = p X k e *
        H X k e (e.toContinuousLinearEquiv (quotientRealPart X k b) -
          Complex.I • e.toContinuousLinearEquiv (quotientImagCoordinate X k b)) := rfl
    _ = p X k e * (quotientMap X k (quotientRealPart X k b) -
        j X k e * quotientMap X k (quotientImagCoordinate X k b)) := by
      rw [map_sub, H_I, H_apply, H_apply,
        ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
    _ = p X k e * quotientMap X k (quotientRealPart X k b) -
        Complex.I • (p X k e * quotientMap X k (quotientImagCoordinate X k b)) := by
      rw [mul_sub, ← mul_assoc, p_j, smul_mul_assoc]
    _ = p X k e * (quotientMap X k (quotientRealPart X k b) -
        Complex.I • quotientMap X k (quotientImagCoordinate X k b)) := by rw [mul_sub, mul_smul_comm]
    _ = p X k e * b := congrArg (p X k e * ·) (quotient_decomposition X k b).symm
    _ = p X k e * b * p X k e := by
      symm
      rw [mul_assoc, ← p_comm, ← mul_assoc, p_sq]

/-- A real Calkin representation of a complex algebra gives an actual
complex Calkin corner representing that algebra. -/
def model : CornerModel A (B X k) (p X k e) where
  inclusion := inclusion X k e
  projection := projection X k e
  inclusion_mul := inclusion_mul X k e
  inclusion_one := inclusion_one X k e
  projection_inclusion := projection_inclusion X k e
  inclusion_projection := inclusion_projection X k e

end NonCalkinAlgebra.RealCalkinCorner
