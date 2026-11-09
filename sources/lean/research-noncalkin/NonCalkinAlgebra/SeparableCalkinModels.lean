import NonCalkinAlgebra.ClosedSubspaceCoding
import NonCalkinAlgebra.CalkinCongruence

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open TopologicalSpace
universe v

instance quotientConventionFintype : Fintype QuotientConvention where
  elems := {.approximable, .compact}
  complete := by intro k; cases k <;> simp

/-- An index set for actual Calkin algebras of all separable Banach spaces,
with either of the paper's two choices of ideal. -/
abbrev SeparableCalkinModel := ClosedEllOneSubspace × QuotientConvention

namespace SeparableCalkinModel
abbrev Carrier (M : SeparableCalkinModel) := OperatorQuotient M.1.Quotient M.2
end SeparableCalkinModel

theorem cardinal_separableCalkinModel_le_continuum :
    Cardinal.mk SeparableCalkinModel ≤ Cardinal.continuum := by
  calc
    Cardinal.mk SeparableCalkinModel =
        Cardinal.mk ClosedEllOneSubspace * Cardinal.mk QuotientConvention := by
      simp only [SeparableCalkinModel, Cardinal.mk_prod, Cardinal.lift_id]
    _ ≤ Cardinal.continuum * Cardinal.continuum := mul_le_mul'
      cardinal_closedEllOneSubspace_le_continuum
      (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

/-- The same Type-0 family models every separable complex Banach space
in every universe. This is a counting statement about isomorphism classes,
not a restriction on the underlying set of the original space. -/
theorem exists_separableCalkinModel (k : QuotientConvention)
    (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] [SeparableSpace X] :
    ∃ M : SeparableCalkinModel, Nonempty (M.Carrier ≃A[ℂ] OperatorQuotient X k) := by
  obtain ⟨N, ⟨e⟩⟩ := exists_ellOne_quotient_equiv X
  exact ⟨(N, k), ⟨calkinCongruence e k⟩⟩

end NonCalkinAlgebra
