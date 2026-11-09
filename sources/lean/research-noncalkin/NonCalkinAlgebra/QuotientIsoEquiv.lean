import NonCalkinAlgebra.CornerTransfer
import NonCalkinAlgebra.RepresentationObstruction
import NonCalkinAlgebra.CalkinCornerData

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u v
namespace OperatorQuotientIso
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {convention : QuotientConvention}
  {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

def toContinuousAlgEquiv (e : OperatorQuotientIso X convention A) :
    OperatorQuotient X convention ≃A[ℂ] A where
  toAlgEquiv := AlgEquiv.ofLinearEquiv e.toContinuousLinearEquiv.toLinearEquiv
    e.map_one_representative e.map_mul
  continuous_toFun := e.toContinuousLinearEquiv.continuous
  continuous_invFun := e.toContinuousLinearEquiv.symm.continuous

def ofContinuousAlgEquiv (e : OperatorQuotient X convention ≃A[ℂ] A) :
    OperatorQuotientIso X convention A where
  toContinuousLinearEquiv := continuousAlgEquivToLinear e
  map_mul_representatives S T := by
    change e (operatorQuotientMap X convention (S * T)) =
      e (operatorQuotientMap X convention S) * e (operatorQuotientMap X convention T)
    rw [operatorQuotientMap_mul, _root_.map_mul e]
  map_one_representative := by
    change e (operatorQuotientMap X convention 1) = 1
    rw [operatorQuotientMap_one, _root_.map_one e]

end OperatorQuotientIso

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {convention : QuotientConvention}
  {A D : Type u} [NormedRing A] [NormedAlgebra ℂ A]
  [NormedRing D] [NormedAlgebra ℂ D]
  {p : A} {e : OperatorQuotient X convention}

/-- The coefficient algebra of a corner is represented on the complemented
range produced by the Calkin-corner lemma. -/
def coefficientQuotientIsoOfCorner (iso : OperatorQuotientIso X convention A)
    (M : CornerModel D A p) (C : CalkinCornerData X convention e)
    (hep : iso.toContinuousLinearEquiv e = p) :
    OperatorQuotientIso C.subspace convention D := by
  have heq : iso.toContinuousAlgEquiv.symm p = e := by
    change iso.toContinuousLinearEquiv.symm p = e
    simpa only [hep] using iso.toContinuousLinearEquiv.symm_apply_apply e
  exact OperatorQuotientIso.ofContinuousAlgEquiv
    (M.transfer C.model iso.toContinuousAlgEquiv.symm heq).symm

end NonCalkinAlgebra
