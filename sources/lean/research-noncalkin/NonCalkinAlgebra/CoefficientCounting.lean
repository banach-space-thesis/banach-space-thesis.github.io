import NonCalkinAlgebra.SeparableCalkinModels
import NonCalkinAlgebra.QuotientIsoEquiv
import NonCalkinAlgebra.PrerequisiteStatements

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open TopologicalSpace SurveyStatements.P2
universe v

/-- The precise cardinal-selection argument: a family of more than continuum
many pairwise nonisomorphic Banach algebras contains one which is not any
separable-space Calkin model. The family itself is an explicit input. -/
theorem exists_member_avoiding_separable_models {I : Type}
    (D : I → ComplexBanachAlgebra.{0})
    (hlarge : Cardinal.continuum < Cardinal.mk I)
    (hdistinct : ∀ i j, Nonempty ((D i).Carrier ≃A[ℂ] (D j).Carrier) → i = j) :
    ∃ i : I, ∀ M : SeparableCalkinModel,
      ¬ Nonempty (M.Carrier ≃A[ℂ] (D i).Carrier) := by
  classical
  by_contra h
  have hrep : ∀ i : I, ∃ M : SeparableCalkinModel,
      Nonempty (M.Carrier ≃A[ℂ] (D i).Carrier) := by
    simpa only [not_exists, not_forall, not_not] using h
  choose M hM using hrep
  have hinj : Function.Injective M := by
    intro i j hij
    obtain ⟨ei⟩ := hM i
    obtain ⟨ej⟩ := hM j
    have ei' : (M j).Carrier ≃A[ℂ] (D i).Carrier := by
      exact hij ▸ ei
    exact hdistinct i j ⟨ei'.symm.trans ej⟩
  have hcard : Cardinal.mk I ≤ Cardinal.mk SeparableCalkinModel := by
    simpa only [Cardinal.lift_id] using Cardinal.mk_le_of_injective hinj
  exact (not_le_of_gt hlarge)
    (hcard.trans cardinal_separableCalkinModel_le_continuum)

/-- This completes the counting part of the coefficient-existence argument.
No AF-algebra abundance theorem or conversion from *-isomorphism classes is
assumed silently: the large family must be supplied as bounded-algebra
isomorphism classes. -/
theorem coefficient_existence_of_large_simple_family {I : Type}
    (D : I → ComplexBanachAlgebra.{0})
    (hlarge : Cardinal.continuum < Cardinal.mk I)
    (hdistinct : ∀ i j, Nonempty ((D i).Carrier ≃A[ℂ] (D j).Carrier) → i = j)
    (hone : ∀ i, ‖(1 : (D i).Carrier)‖ = 1)
    (hdensity : ∀ i, HasDensityCharacter (D i).Carrier Cardinal.continuum)
    (hsimple : ∀ i, IsTopologicallySimple (D i).Carrier) :
    CoefficientExistenceStatement.{v} := by
  obtain ⟨i, hi⟩ := exists_member_avoiding_separable_models D hlarge hdistinct
  refine ⟨D i, hone i, hdensity i, hsimple i, ?_⟩
  intro k Y _ _ _ _
  rintro ⟨iso⟩
  obtain ⟨M, ⟨e⟩⟩ := exists_separableCalkinModel k Y
  exact hi M ⟨e.trans iso.toContinuousAlgEquiv⟩

end NonCalkinAlgebra
