import ThesisCommon.Analysis.L1BoundedApproximationWeakCompact
import ThesisCommon.Analysis.L1CutModulus
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! The sufficient Dunford-Pettis direction on finite real L1 spaces.
Uniform integrability gives bounded truncations uniformly in the family;
their ell-one column operators factor through L2 and converge in norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {Y I : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]

theorem UniformIntegrable.exists_lOne_bounded_approximation
    {f : I → Lp ℝ 1 ν} (hUI : UniformIntegrable (fun i => (f i : Y → ℝ)) 1 ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : I → Lp ℝ 1 ν) (C : ℝ), 0 ≤ C ∧
      (∀ i, ∀ᵐ y ∂ν, ‖g i y‖ ≤ C) ∧ ∀ i, ‖f i - g i‖ ≤ ε := by
  obtain ⟨C, hC⟩ := hUI.spec (by norm_num) (by norm_num) hε
  let A : I → Set Y := fun i => {y | C ≤ ‖f i y‖₊}
  have hA (i : I) : MeasurableSet (A i) :=
    measurableSet_le measurable_const (Lp.stronglyMeasurable (f i)).nnnorm.measurable
  let g := fun i => lpCut (A i)ᶜ (hA i).compl (f i)
  refine ⟨g, C, C.coe_nonneg, ?_, ?_⟩
  · intro i
    filter_upwards [lpCut_coe (A i)ᶜ (hA i).compl (f i)] with y hy
    change ‖lpCut (A i)ᶜ (hA i).compl (f i) y‖ ≤ (C : ℝ)
    rw [hy]
    by_cases ha : y ∈ A i
    · simp only [mem_compl_iff, ha, not_true_eq_false, not_false_eq_true,
        indicator_of_notMem, norm_zero]
      exact C.coe_nonneg
    · rw [indicator_of_mem ha]
      exact (show ‖f i y‖₊ < C from lt_of_not_ge ha).le
  · intro i
    have heq : f i - g i = lpCut (A i) (hA i) (f i) := by
      rw [sub_eq_iff_eq_add]
      exact (lOneCut_add_compl (A i) (hA i) (f i)).symm
    rw [heq]
    change ‖((Lp.memLp (f i)).indicator (hA i)).toLp ((A i).indicator (f i))‖ ≤ ε
    rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC i)).trans_eq
      (ENNReal.toReal_ofReal hε.le)

theorem isCompact_weakClosure_range_of_uniformIntegrable
    (f : I → Lp ℝ 1 ν) (hUI : UniformIntegrable (fun i => (f i : Y → ℝ)) 1 ν) :
    IsCompact (closure ((toWeakSpace ℝ (Lp ℝ 1 ν)) '' Set.range f)) := by
  obtain ⟨M, hM⟩ := hUI.2.2
  have hnorm (i : I) : ‖f i‖ ≤ (M : ℝ) := by
    rw [Lp.norm_def]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (hM i)
  exact isCompact_weakClosure_range_of_bounded_approximations f M M.coe_nonneg hnorm
    (fun _ hε => UniformIntegrable.exists_lOne_bounded_approximation hUI hε)

end ThesisCommon
