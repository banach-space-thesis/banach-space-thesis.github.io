import NonCalkinAlgebra.RetractionOperatorIdeals
import NonCalkinAlgebra.QuotientLinearMap
import NonCalkinAlgebra.QuotientAlgebra
import NonCalkinAlgebra.CornerModel

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u v
namespace BoundedRetraction
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  (s : BoundedRetraction X Y) (convention : QuotientConvention)

def extendQuotient : OperatorQuotient Y convention →L[ℂ] OperatorQuotient X convention :=
  quotientLinearMap (operatorIdeal Y convention) (operatorIdeal X convention)
    s.extendOperators (fun T hT => s.operatorIdeal_extend convention hT)

def compressQuotient : OperatorQuotient X convention →L[ℂ] OperatorQuotient Y convention :=
  quotientLinearMap (operatorIdeal X convention) (operatorIdeal Y convention)
    s.compressOperators (fun T hT => s.operatorIdeal_compress convention hT)

@[simp] theorem extendQuotient_mk (T : BoundedOperators Y) :
    s.extendQuotient convention (operatorQuotientMap Y convention T) =
      operatorQuotientMap X convention (s.extendOperators T) := rfl

@[simp] theorem compressQuotient_mk (T : BoundedOperators X) :
    s.compressQuotient convention (operatorQuotientMap X convention T) =
      operatorQuotientMap Y convention (s.compressOperators T) := rfl

theorem extendQuotient_mul (a b : OperatorQuotient Y convention) :
    s.extendQuotient convention (a * b) =
      s.extendQuotient convention a * s.extendQuotient convention b := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  change s.extendQuotient convention (operatorQuotientMap Y convention (S * T)) = _
  rw [s.extendQuotient_mk, s.extendOperators_mul, operatorQuotientMap_mul]
  rfl

theorem extendQuotient_one : s.extendQuotient convention 1 =
    operatorQuotientMap X convention s.projectionOperator := by
  change s.extendQuotient convention (operatorQuotientMap Y convention 1) = _
  rw [s.extendQuotient_mk, s.extendOperators_one]

theorem compress_extend_quotient (a : OperatorQuotient Y convention) :
    s.compressQuotient convention (s.extendQuotient convention a) = a := by
  refine Quotient.inductionOn a ?_
  intro T
  change s.compressQuotient convention
    (s.extendQuotient convention (operatorQuotientMap Y convention T)) = _
  rw [s.extendQuotient_mk, s.compressQuotient_mk, s.compress_extend]
  rfl

theorem extend_compress_quotient (a : OperatorQuotient X convention) :
    s.extendQuotient convention (s.compressQuotient convention a) =
      operatorQuotientMap X convention s.projectionOperator * a *
        operatorQuotientMap X convention s.projectionOperator := by
  refine Quotient.inductionOn a ?_
  intro T
  change s.extendQuotient convention
    (s.compressQuotient convention (operatorQuotientMap X convention T)) = _
  rw [s.compressQuotient_mk, s.extendQuotient_mk, s.extend_compress,
    operatorQuotientMap_mul, operatorQuotientMap_mul]
  rfl

/-- The corner identification for a genuine complemented subspace, valid
for both choices of operator ideal. Idempotent lifting is not used here. -/
def quotientCornerModel : CornerModel (OperatorQuotient Y convention)
    (OperatorQuotient X convention) (operatorQuotientMap X convention s.projectionOperator) where
  inclusion := s.extendQuotient convention
  projection := s.compressQuotient convention
  inclusion_mul := s.extendQuotient_mul convention
  inclusion_one := s.extendQuotient_one convention
  projection_inclusion := s.compress_extend_quotient convention
  inclusion_projection := s.extend_compress_quotient convention

end BoundedRetraction
end NonCalkinAlgebra
