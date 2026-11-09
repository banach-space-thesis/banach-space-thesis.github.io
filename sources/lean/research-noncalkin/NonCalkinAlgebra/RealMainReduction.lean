import NonCalkinAlgebra.RealCalkinCorner
import NonCalkinAlgebra.CalkinCornerTheorems
import NonCalkinAlgebra.QuotientIsoEquiv
import NonCalkinAlgebra.MainFromCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open BanachComplexification SurveyStatements.P2
universe u v

/-- A complex algebra which is never a complex Calkin algebra is never a
real Calkin algebra after forgetting complex scalars. Both selected ideals
are handled by the actual complexification and lifting constructions. -/
theorem not_real_representable_of_not_complex
    {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    (k : QuotientConvention)
    (hA : ∀ (Y : Type v) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y],
      ¬ Nonempty (OperatorQuotientIso Y k A))
    (X : Type v) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
    ¬ Nonempty (RealOperatorQuotientIso X k A) := by
  rintro ⟨e⟩
  let M := RealCalkinCorner.model X k e
  obtain ⟨C⟩ := calkin_corner (BanachComplexification X) k
    (RealCalkinCorner.p X k e) (RealCalkinCorner.p_sq X k e)
  let E : A ≃A[ℂ] OperatorQuotient C.subspace k :=
    M.transfer C.model (ContinuousAlgEquiv.refl ℂ (OperatorQuotient (BanachComplexification X) k)) rfl
  exact hA C.subspace ⟨OperatorQuotientIso.ofContinuousAlgEquiv E.symm⟩

/-- The complete real argument of Remark 1.2, conditional only on the complex
main theorem. The witness is the underlying real algebra of the same A. -/
theorem real_main_of_complex_main (h : MainStatement.{v}) : RealMainStatement.{v} := by
  obtain ⟨A, hdensity, hideals, havoid⟩ := h
  refine ⟨underlyingRealBanachAlgebra A, underlying_real_density A _ hdensity,
    underlying_real_ideal_structure A hideals, ?_⟩
  intro k X _ _ _
  exact not_real_representable_of_not_complex k (havoid k) X

/-- Both main statements now reduce to the same single missing coefficient
existence input. This theorem does not assert that the input is proved. -/
theorem real_main_of_coefficient_existence (h : CoefficientExistenceStatement.{v}) :
    RealMainStatement.{v} :=
  real_main_of_complex_main (main_of_coefficient_existence h)

end NonCalkinAlgebra
