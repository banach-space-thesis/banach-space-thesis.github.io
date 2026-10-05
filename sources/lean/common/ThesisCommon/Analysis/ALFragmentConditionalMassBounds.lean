import ThesisCommon.Analysis.ALFragmentConditionalMass

/-! Size and unit bounds for the actual conditional mass of a fragment. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

theorem norm_alFragmentConditionalMass (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (a : PositiveFragmentAlgebra e) :
    ‖alFragmentConditionalMass hAL e S a‖ = ‖positiveFragmentValue a‖ := by
  rw [alFragmentConditionalMass,
    norm_lOneSubsigmaProjection_of_nonneg _ _ (alFragmentIndicator_nonneg hAL e a),
    alFragmentIndicator_eq_lOneIndicator, norm_lOneIndicator,
    Measure.real, alFragmentMeasure_apply, ENNReal.toReal_ofReal (norm_nonneg _)]

omit [HasSolidNorm E] in
theorem alFragmentConditionalMass_top (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :
    alFragmentConditionalMass hAL e S ⊤ = alFragmentIndicator hAL e ⊤ := by
  apply lOneSubsigmaProjection_eq_self
  rw [alFragmentIndicator_eq_lOneIndicator]
  exact (stronglyMeasurable_const.indicator
    (measurableSet_booleanStoneSet_of_mem_subalgebra S S.top_mem)).aestronglyMeasurable.congr
      (lOneIndicator_coe _ _).symm

theorem alFragmentConditionalMass_le_top (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (a : PositiveFragmentAlgebra e) :
    alFragmentConditionalMass hAL e S a ≤ alFragmentConditionalMass hAL e S ⊤ := by
  exact lOneSubsigmaProjection_mono _ _ ((alFragmentIndicator_le_iff hAL e _ _).mpr le_top)

end ThesisCommon

