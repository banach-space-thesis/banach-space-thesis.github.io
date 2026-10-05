import ThesisCommon.Analysis.GowersMaureyStrictlySingularIdeal
import ThesisCommon.Analysis.GowersMaureyWienerCompletion
import ThesisCommon.Analysis.GowersMaureyStrictlySingularKernel

/-! Strict singularity is unchanged by an actual zero-seminorm error.
For an approximable operator this reduces the remaining converse kernel
question exactly to its genuine Laurent representative. No claim that a
nonzero Laurent operator is non-strictly-singular is assumed or asserted. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem strictlySingular_iff_of_spaceOperatorSeminorm_sub_zero
    (D : ConstructionData 𝕜) (S T : ShiftSpace D →L[𝕜] ShiftSpace D)
    (h : spaceOperatorSeminorm D (S-T) = 0) :
    IsStrictlySingularOperator S ↔ IsStrictlySingularOperator T := by
  have he := isStrictlySingularOperator_of_spaceOperatorSeminorm_zero D (S-T) h
  constructor
  · intro hS
    simpa only [sub_sub_cancel] using strictlySingular_sub D hS he
  · intro hT
    simpa only [sub_add_cancel] using strictlySingular_add D he hT

theorem strictlySingular_iff_laurent_of_representative
    (D : ConstructionData 𝕜) (T : ShiftSpace D →L[𝕜] ShiftSpace D)
    (a : WienerSequences 𝕜)
    (ha : spaceOperatorSeminorm D (T-laurentOperator D a) = 0) :
    IsStrictlySingularOperator T ↔ IsStrictlySingularOperator (laurentOperator D a) :=
  strictlySingular_iff_of_spaceOperatorSeminorm_sub_zero D T (laurentOperator D a) ha

theorem IsFiniteSpreadApproximable.exists_strictlySingular_laurent_representative
    {D : ConstructionData 𝕜} {T : ShiftSpace D →L[𝕜] ShiftSpace D}
    (happrox : IsFiniteSpreadApproximable D T) (hT : IsStrictlySingularOperator T) :
    ∃ a : WienerSequences 𝕜, spaceOperatorSeminorm D (T-laurentOperator D a) = 0 ∧
      ‖a‖ = spaceOperatorSeminorm D T ∧ IsStrictlySingularOperator (laurentOperator D a) := by
  obtain ⟨a,ha,_⟩ := happrox.exists_unique_wiener_representative
  exact ⟨a,ha,wiener_representative_norm D ha,
    (strictlySingular_iff_laurent_of_representative D T a ha).mp hT⟩

end ThesisCommon.GowersMaurey
