import NonCalkinAlgebra.IdempotentLifting
import NonCalkinAlgebra.CalkinCornersFromLifting
import NonCalkinAlgebra.SeparableRangeQuotient

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open TopologicalSpace
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (convention : QuotientConvention)

/-- Lemma 3.1, with the lifting theorem discharged. -/
theorem calkin_corner (e : OperatorQuotient X convention) (he : e * e = e) :
    Nonempty (CalkinCornerData X convention e) :=
  calkin_corner_from_lifting idempotent_lifting X convention e he

theorem separable_calkin_corner [SeparableSpace X]
    (e : OperatorQuotient X convention) (he : e * e = e) :
    ∃ C : CalkinCornerData X convention e, SeparableSpace C.subspace :=
  separable_calkin_corner_from_lifting idempotent_lifting X convention e he

/-- Lemma 3.3, in the paper's actual separable-range quotient ideal. -/
theorem separable_range_calkin_corner (e : OperatorQuotient X convention) (he : e * e = e)
    (hsep : e ∈ separableRangeQuotientIdeal X convention) :
    ∃ C : CalkinCornerData X convention e, SeparableSpace C.subspace :=
  separable_range_calkin_corner_from_lifting idempotent_lifting X convention e he
    (exists_separable_representative X convention hsep)

end NonCalkinAlgebra
