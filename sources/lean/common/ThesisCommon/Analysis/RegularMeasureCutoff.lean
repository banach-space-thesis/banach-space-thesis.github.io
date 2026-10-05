import ThesisCommon.Analysis.ContinuousMapRiesz
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Sharp continuous cutoff witnesses for the mass of an open set. These
use actual inner regularity and Urysohn functions on compact Hausdorff spaces. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

theorem exists_continuousMap_open_mass_test (μ : Measure K)
    [IsFiniteMeasure μ] [μ.Regular] {U : Set K} (hU : IsOpen U)
    {r : ℝ} (hr : r < μ.real U) :
    ∃ f : C(K, ℝ), (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∉ U, f x = 0) ∧ r < ∫ x, f x ∂μ := by
  by_cases hr0 : r < 0
  · exact ⟨0, by simp, by simp, by simpa using hr0⟩
  have hr0' : 0 ≤ r := le_of_not_gt hr0
  have hr' : ENNReal.ofReal r < μ U := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal hr0' (measure_ne_top μ U)).mpr hr
  obtain ⟨F, hFU, hFc, hFmass⟩ := hU.exists_lt_isCompact hr'
  obtain ⟨f, hfF, hfU, _, hf⟩ := exists_continuous_one_zero_of_isCompact
    hFc hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hFU)
  refine ⟨f, hf, fun x hx => hfU hx, ?_⟩
  have hmass : r < μ.real F := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal hr0' (measure_ne_top μ F)).mp hFmass
  have hfi : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have heq : ∫ x in F, f x ∂μ = μ.real F := by
    rw [setIntegral_congr_fun hFc.measurableSet hfF]
    simp
  exact hmass.trans_le (heq.symm.trans_le
    (setIntegral_le_integral hfi (Filter.Eventually.of_forall fun x => (hf x).1)))

theorem exists_continuousMap_riesz_open_test (Λ : C(K, ℝ) →ₚ[ℝ] ℝ)
    {U : Set K} (hU : IsOpen U) {r : ℝ}
    (hr : r < (continuousMapRieszMeasure Λ).real U) :
    ∃ f : C(K, ℝ), (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∉ U, f x = 0) ∧ r < Λ f := by
  obtain ⟨f, hf, hfs, hfr⟩ := exists_continuousMap_open_mass_test
    (continuousMapRieszMeasure Λ) hU hr
  exact ⟨f, hf, hfs, by simpa only [integral_continuousMapRieszMeasure] using hfr⟩

end ThesisCommon
