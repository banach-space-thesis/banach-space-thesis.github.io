import SurveyStatements.P2InvariantQuotient
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The sum of a closed complex subspace and one scalar line is closed. -/
theorem closed_scalar_extension (N : Submodule ℂ E) [IsClosed (N : Set E)] (v : E) :
    IsClosed (((Submodule.span ℂ {N.mkQ v}).comap N.mkQ : Submodule ℂ E) : Set E) := by
  let S : Submodule ℂ (E ⧸ N) := Submodule.span ℂ {N.mkQ v}
  letI : FiniteDimensional ℂ S := by dsimp [S]; infer_instance
  have hS : IsClosed (S : Set (E ⧸ N)) := S.closed_of_finiteDimensional
  let q : E →L[ℂ] E ⧸ N := SurveyStatements.P2.quotientProjection N
  exact hS.preimage q.continuous

end NonCalkinAlgebra
