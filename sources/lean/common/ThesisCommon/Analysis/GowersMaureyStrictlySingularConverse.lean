import ThesisCommon.Analysis.GowersMaureyLaurentNotStrictlySingular
import ThesisCommon.Analysis.GowersMaureyStrictlySingularRepresentatives

/-! The converse strict-singularity/kernel inclusion for the actual complex
shift space, under precisely the genuine finite-spread approximation input
for the operator in question. The Laurent obstruction has been proved on
actual infinite-dimensional subspaces, not assumed as a representation field. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem spaceOperatorSeminorm_zero_of_strictlySingular_of_approximable
    {D : ConstructionData ℂ} {T : ShiftSpace D →L[ℂ] ShiftSpace D}
    (happrox : IsFiniteSpreadApproximable D T) (hT : IsStrictlySingularOperator T) :
    spaceOperatorSeminorm D T = 0 := by
  obtain ⟨a,_,hn,hSS⟩ := happrox.exists_strictlySingular_laurent_representative hT
  have ha : a = 0 := by
    by_contra h
    exact not_strictlySingular_laurent_of_ne_zero D a h hSS
  rw [← hn, ha, norm_zero]

theorem spaceOperatorSeminorm_zero_iff_strictlySingular_of_approximable
    {D : ConstructionData ℂ} {T : ShiftSpace D →L[ℂ] ShiftSpace D}
    (happrox : IsFiniteSpreadApproximable D T) :
    spaceOperatorSeminorm D T = 0 ↔ IsStrictlySingularOperator T :=
  ⟨isStrictlySingularOperator_of_spaceOperatorSeminorm_zero D T,
    spaceOperatorSeminorm_zero_of_strictlySingular_of_approximable happrox⟩

end ThesisCommon.GowersMaurey
