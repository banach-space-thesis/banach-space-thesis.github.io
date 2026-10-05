import ThesisCommon.Analysis.ALSubalgebraMeasureTransport
import ThesisCommon.Analysis.L1SubsigmaTransport
import ThesisCommon.Analysis.ALFragmentConditionalMassBounds

/-! Transport a genuine conditional budget across an isomorphism of closed
fragment subalgebras. Every prescribed base intersection mass is preserved. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
  [HasSolidNorm F] [CompleteSpace F]
variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]
variable (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (f : F) [Fact (0 ≤ f)]

include hE in
theorem exists_transported_conditional_budget
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (T : BooleanSubalgebra (PositiveFragmentAlgebra f))
    (hT : IsClosed (T : Set (PositiveFragmentAlgebra f)))
    (φ : S ≃o T)
    (hφ : ∀ s : S, ‖positiveFragmentValue (φ s).val‖ = ‖positiveFragmentValue s.val‖)
    (a : PositiveFragmentAlgebra e) :
    ∃ g : Lp ℝ 1 (alFragmentMeasure hF f),
      AEStronglyMeasurable[booleanSubalgebraStoneMeasurableSpace T] g (alFragmentMeasure hF f) ∧
      0 ≤ g ∧ g ≤ alFragmentConditionalMass hF f T ⊤ ∧
      ∀ s : S, ‖lpCut (booleanStoneSet (φ s).val) (measurableSet_booleanStoneSet _) g‖ =
        ‖positiveFragmentValue (a ⊓ s.val)‖ := by
  let μ := alFragmentMeasure hE e
  let ν := alFragmentMeasure hF f
  let hm := booleanSubalgebraStoneMeasurableSpace_le S
  let hn := booleanSubalgebraStoneMeasurableSpace_le T
  let Φ := alSubalgebraMeasureAlgebraIso hE e hF f S hS T hT φ hφ
  let U := lOneSubsigmaTransport μ ν hm hn Φ
  have hclass (s : S) := alSubalgebraMeasureAlgebraIso_class hE e hF f S hS T hT φ hφ s
  have hunit : U (alFragmentConditionalMass hE e S ⊤) =
      alFragmentConditionalMass hF f T ⊤ := by
    rw [alFragmentConditionalMass_top, alFragmentConditionalMass_top,
      alFragmentIndicator_eq_lOneIndicator, alFragmentIndicator_eq_lOneIndicator]
    apply lOneSubsigmaTransport_indicator μ ν hm hn Φ _
      (measurableSet_booleanStoneSet_of_mem_subalgebra S S.top_mem) _
      (measurableSet_booleanStoneSet_of_mem_subalgebra T T.top_mem)
    simpa only [alSubalgebraClass, TopHomClass.map_top, BooleanSubalgebra.val_top] using hclass (⊤ : S)
  let g := U (alFragmentConditionalMass hE e S a)
  refine ⟨g, lOneSubsigmaTransport_mem μ ν hm hn Φ _,
    lOneSubsigmaTransport_nonneg μ ν hm hn Φ (alFragmentConditionalMass_nonneg hE e S a), ?_, ?_⟩
  · have hpos := lOneSubsigmaTransport_nonneg μ ν hm hn Φ
      (sub_nonneg.mpr (alFragmentConditionalMass_le_top hE e S a))
    change 0 ≤ U (alFragmentConditionalMass hE e S ⊤ - alFragmentConditionalMass hE e S a) at hpos
    rw [map_sub, hunit] at hpos
    exact sub_nonneg.mp hpos
  · intro s
    have hcut := lOneSubsigmaTransport_cut μ ν hm hn Φ
      (booleanStoneSet s.val) (measurableSet_booleanStoneSet_of_mem_subalgebra S s.property)
      (booleanStoneSet (φ s).val) (measurableSet_booleanStoneSet_of_mem_subalgebra T (φ s).property)
      (hclass s) (alFragmentConditionalMass hE e S a)
    change ‖lpCut (booleanStoneSet (φ s).val) _
      (lOneSubsigmaTransport μ ν hm hn Φ (alFragmentConditionalMass hE e S a))‖ = _
    rw [← hcut, ← alFragmentConditionalMass_inf_of_mem hE e S a s.val s.property,
      lOneSubsigmaTransport_norm μ ν hm hn Φ _
        (alFragmentConditionalMass_aestronglyMeasurable hE e S (a ⊓ s.val)),
      norm_alFragmentConditionalMass]

end ThesisCommon

