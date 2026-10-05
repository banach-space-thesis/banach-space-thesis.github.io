import ThesisCommon.Analysis.ComplexL1UniformIntegrableWeakCompact
import ThesisCommon.Analysis.WeakCompactSubsequence

/-! Uniformly integrable sequences in finite L1 spaces have actual weakly
convergent subsequences, for both scalars and arbitrary measurable spaces. -/
noncomputable section
open MeasureTheory Filter Topology
namespace ThesisCommon
variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]

theorem exists_real_lOne_weak_subsequence_of_uniformIntegrable
    (f : ℕ → Lp ℝ 1 ν) (hUI : UniformIntegrable (fun n => (f n : Y → ℝ)) 1 ν) :
    ∃ x : Lp ℝ 1 ν, ∃ r : ℕ → ℕ, StrictMono r ∧
      Tendsto (fun n => toWeakSpace ℝ (Lp ℝ 1 ν) (f (r n))) atTop
        (𝓝 (toWeakSpace ℝ (Lp ℝ 1 ν) x)) :=
  exists_weak_subsequence_of_compactClosure f
    (isCompact_weakClosure_range_of_uniformIntegrable f hUI)

theorem exists_complex_lOne_weak_subsequence_of_uniformIntegrable
    (f : ℕ → Lp ℂ 1 ν) (hUI : UniformIntegrable (fun n => (f n : Y → ℂ)) 1 ν) :
    ∃ x : Lp ℂ 1 ν, ∃ r : ℕ → ℕ, StrictMono r ∧
      Tendsto (fun n => toWeakSpace ℂ (Lp ℂ 1 ν) (f (r n))) atTop
        (𝓝 (toWeakSpace ℂ (Lp ℂ 1 ν) x)) :=
  exists_weak_subsequence_of_compactClosure f
    (isCompact_weakClosure_range_of_complex_uniformIntegrable f hUI)

end ThesisCommon
