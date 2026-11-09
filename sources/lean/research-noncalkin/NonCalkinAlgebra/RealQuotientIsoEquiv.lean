import NonCalkinAlgebra.RealStatements
import NonCalkinAlgebra.RealQuotientAlgebra
import Mathlib.Topology.Algebra.Algebra.Equiv

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.RealOperatorQuotientIso
universe u v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {k : QuotientConvention} {A : Type u} [NormedRing A] [NormedAlgebra ℝ A]

theorem map_mul (e : RealOperatorQuotientIso X k A) (a b : RealOperatorQuotient X k) :
    e.toContinuousLinearEquiv (a * b) =
      e.toContinuousLinearEquiv a * e.toContinuousLinearEquiv b := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  exact e.map_mul_representatives S T

def toContinuousAlgEquiv (e : RealOperatorQuotientIso X k A) :
    RealOperatorQuotient X k ≃A[ℝ] A where
  toAlgEquiv := AlgEquiv.ofLinearEquiv e.toContinuousLinearEquiv.toLinearEquiv
    e.map_one_representative e.map_mul
  continuous_toFun := e.toContinuousLinearEquiv.continuous
  continuous_invFun := e.toContinuousLinearEquiv.symm.continuous

end NonCalkinAlgebra.RealOperatorQuotientIso
