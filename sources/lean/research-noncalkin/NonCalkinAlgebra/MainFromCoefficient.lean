import NonCalkinAlgebra.MainReduction
import NonCalkinAlgebra.IdempotentLifting

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe v

/-- Theorem 1.1 after supplying only the coefficient existence theorem.
Lifting, corners, construction and final assembly have actual proofs. -/
theorem main_of_coefficient_existence (hD : CoefficientExistenceStatement.{v}) :
    MainStatement.{v} :=
  main_from_prerequisites hD idempotent_lifting

end NonCalkinAlgebra
