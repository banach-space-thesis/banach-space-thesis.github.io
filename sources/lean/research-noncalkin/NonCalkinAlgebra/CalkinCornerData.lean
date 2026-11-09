import NonCalkinAlgebra.RetractionCalkinCorner
import NonCalkinAlgebra.ProjectionRange

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2 Set TopologicalSpace
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The literal corner realisation from Section 3: a closed complemented
subspace of X and bounded inverse algebra maps for the actual operator
quotient corner, with the selected ideal fixed on both spaces. -/
structure CalkinCornerData (convention : QuotientConvention)
    (e : OperatorQuotient X convention) where
  subspace : Submodule ℂ X
  closed : IsClosed (subspace : Set X)
  complemented : subspace.ClosedComplemented
  [completeSpace : CompleteSpace subspace]
  model : CornerModel (OperatorQuotient subspace convention) (OperatorQuotient X convention) e

attribute [instance] CalkinCornerData.completeSpace

namespace BoundedProjection
variable {X} (P : BoundedProjection X) (convention : QuotientConvention)

def calkinCornerData : CalkinCornerData X convention (operatorQuotientMap X convention P.operator) where
  subspace := P.range
  closed := P.range_isClosed
  complemented := P.range_closedComplemented
  completeSpace := inferInstance
  model := by
    simpa only [P.rangeRetraction_projectionOperator] using
      P.rangeRetraction.quotientCornerModel convention

end BoundedProjection
end NonCalkinAlgebra
