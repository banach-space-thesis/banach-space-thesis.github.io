import ThesisCommon.Analysis.ALFragmentSubalgebraMeasurable

/-! The indicators belonging to a generated sub-sigma algebra are exactly
the indicators of the metric-closed Boolean fragment subalgebra. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon

theorem aestronglyMeasurable_lOneIndicator_iff_measurable_representative
    {X : Type*} {m : MeasurableSpace X} [m₀ : MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (A : Set X) (hA : MeasurableSet[m₀] A) :
    AEStronglyMeasurable[m] (lOneIndicator μ A hA : X → ℝ) μ ↔
      ∃ s : Set X, MeasurableSet[m] s ∧ A =ᵐ[μ] s := by
  constructor
  · intro hf
    let g := hf.mk (lOneIndicator μ A hA : X → ℝ)
    refine ⟨{x | (1 / 2 : ℝ) < g x}, ?_, ?_⟩
    · exact measurableSet_lt measurable_const hf.stronglyMeasurable_mk.measurable
    · filter_upwards [hf.ae_eq_mk, lOneIndicator_coe (μ := μ) A hA] with x hx hix
      have hg : g x = A.indicator (fun _ => (1 : ℝ)) x := hx.symm.trans hix
      change (x ∈ A) = ((1 / 2 : ℝ) < g x)
      rw [hg]
      by_cases h : x ∈ A <;> norm_num [h]
  · rintro ⟨s, hs, has⟩
    have hi : StronglyMeasurable[m] (s.indicator (fun _ : X => (1 : ℝ))) :=
      stronglyMeasurable_const.indicator hs
    apply hi.aestronglyMeasurable.congr
    filter_upwards [has, lOneIndicator_coe (μ := μ) A hA] with x hx hix
    rw [hix]
    change (x ∈ A) = (x ∈ s) at hx
    by_cases h : x ∈ A <;> simp_all

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

theorem aestronglyMeasurable_alFragmentIndicator_iff_mem
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e))) (a : PositiveFragmentAlgebra e) :
    AEStronglyMeasurable[booleanSubalgebraStoneMeasurableSpace S]
      (alFragmentIndicator hAL e a : BooleanStonePoint (PositiveFragmentAlgebra e) → ℝ)
      (alFragmentMeasure hAL e) ↔ a ∈ S := by
  rw [alFragmentIndicator_eq_lOneIndicator,
    aestronglyMeasurable_lOneIndicator_iff_measurable_representative]
  exact (mem_closed_subalgebra_iff_measurable_representative hAL e S hS a).symm

end ThesisCommon
