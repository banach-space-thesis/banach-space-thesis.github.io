import NonCalkinAlgebra.CalkinCornerData
import NonCalkinAlgebra.PrerequisiteStatements

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2 Set TopologicalSpace
universe v
variable (hLift : IdempotentLiftingStatement.{v})
  (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (convention : QuotientConvention)

include hLift

theorem idempotent_representative_from_lifting
    (e : OperatorQuotient X convention) (he : e * e = e) :
    ∃ P : BoundedProjection X, operatorQuotientMap X convention P.operator = e := by
  obtain ⟨T, hT⟩ := Submodule.mkQ_surjective (operatorIdeal X convention) e
  have hT' : operatorQuotientMap X convention T = e := hT
  have hdefect : T * T - T ∈ operatorIdeal X convention := by
    apply (operatorQuotientMap_eq_zero X convention _).mp
    rw [map_sub, operatorQuotientMap_mul, hT', he, sub_self]
  obtain ⟨P, hP, hPT⟩ := hLift convention X T hdefect
  refine ⟨⟨P, hP⟩, ?_⟩
  have hz := (operatorQuotientMap_eq_zero X convention (P - T)).mpr hPT
  rw [map_sub, sub_eq_zero] at hz
  exact hz.trans hT'

/-- Lemma 3.1 after the spectral lifting theorem is supplied as a proved
input. This helper does not assert the outstanding lifting theorem. -/
theorem calkin_corner_from_lifting (e : OperatorQuotient X convention) (he : e * e = e) :
    Nonempty (CalkinCornerData X convention e) := by
  obtain ⟨P, hP⟩ := idempotent_representative_from_lifting hLift X convention e he
  exact ⟨hP ▸ P.calkinCornerData convention⟩

theorem separable_calkin_corner_from_lifting [SeparableSpace X]
    (e : OperatorQuotient X convention) (he : e * e = e) :
    ∃ C : CalkinCornerData X convention e, SeparableSpace C.subspace := by
  obtain ⟨P, hP⟩ := idempotent_representative_from_lifting hLift X convention e he
  subst e
  exact ⟨P.calkinCornerData convention, P.range_separableSpace⟩

/-- Lemma 3.3: a separable-range representative forces the complemented
range to be separable, with no separability assumption on X. -/
theorem separable_range_calkin_corner_from_lifting
    (e : OperatorQuotient X convention) (he : e * e = e)
    (hrep : ∃ T : BoundedOperators X,
      IsSeparable (Set.range T) ∧ operatorQuotientMap X convention T = e) :
    ∃ C : CalkinCornerData X convention e, SeparableSpace C.subspace := by
  obtain ⟨T, hTsep, hT⟩ := hrep
  have hdefect : T * T - T ∈ operatorIdeal X convention := by
    apply (operatorQuotientMap_eq_zero X convention _).mp
    rw [map_sub, operatorQuotientMap_mul, hT, he, sub_self]
  obtain ⟨P, hP, hPT⟩ := hLift convention X T hdefect
  let Q : BoundedProjection X := ⟨P, hP⟩
  have hQ : operatorQuotientMap X convention Q.operator = e := by
    have hz := (operatorQuotientMap_eq_zero X convention (P - T)).mpr hPT
    rw [map_sub, sub_eq_zero] at hz
    exact hz.trans hT
  have hPsep : IsSeparable (Set.range P) := by
    have hdiff := compactOperator_range_isSeparable (operatorIdeal_le_compact X convention hPT)
    have hsum := isSeparableRange_add hTsep hdiff
    have hsumEq : T + (P - T) = P := by abel
    rwa [hsumEq] at hsum
  have hQsep : SeparableSpace Q.range := Q.range_separable_of_separableRange hPsep
  cases hQ
  exact ⟨Q.calkinCornerData convention, hQsep⟩

end NonCalkinAlgebra
