import ThesisCommon.Analysis.ContinuousMapModulusTest
import ThesisCommon.Analysis.RegularMeasureCutoff

/-! Actual finite regular measures representing the sharp dual moduli.
Open-set mass gives continuous scalar test functions with the same strict
lower bound and support inside that open set, over both scalar fields. -/
noncomputable section
open Set MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

def continuousMapRealModulusMeasure (φ : C(K, ℝ) →L[ℝ] ℝ) : Measure K :=
  continuousMapRieszMeasure (PositiveLinearMap.mk₀ (dualModulus φ).toLinearMap
    ((operator_nonneg_iff _).mp (dualModulus_nonneg φ)))

instance continuousMapRealModulusMeasure_finite (φ : C(K, ℝ) →L[ℝ] ℝ) :
    IsFiniteMeasure (continuousMapRealModulusMeasure φ) := by
  unfold continuousMapRealModulusMeasure
  infer_instance

instance continuousMapRealModulusMeasure_regular (φ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRealModulusMeasure φ).Regular := by
  unfold continuousMapRealModulusMeasure
  infer_instance

theorem continuousMapRealModulusMeasure_mass (φ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRealModulusMeasure φ).real univ = ‖φ‖ := by
  rw [continuousMapRealModulusMeasure, continuousMapRieszMeasure_mass]
  exact (norm_positive_continuousMapDual _ (dualModulus_nonneg φ)).symm.trans
    (norm_dualModulus φ)

theorem exists_continuousMap_real_open_modulus_test (φ : C(K, ℝ) →L[ℝ] ℝ)
    {U : Set K} (hU : IsOpen U) {r : ℝ}
    (hr : r < (continuousMapRealModulusMeasure φ).real U) :
    ∃ g : C(K, ℝ), ‖g‖ ≤ 1 ∧ (∀ x ∉ U, g x = 0) ∧ r < ‖φ g‖ := by
  obtain ⟨f, hf, hfs, hfr⟩ := exists_continuousMap_riesz_open_test _ hU hr
  obtain ⟨g, hg, hgr⟩ := exists_dualModulus_test φ
    (show 0 ≤ f from fun x => (hf x).1) hfr
  refine ⟨g, (ContinuousMap.norm_le _ zero_le_one).mpr (fun x => (hg x).trans (hf x).2),
    ?_, hgr.trans_le (le_abs_self _)⟩
  intro x hx
  apply norm_eq_zero.mp
  exact le_antisymm ((hg x).trans_eq (hfs x hx)) (norm_nonneg _)

def continuousMapComplexModulusMeasure (φ : C(K, ℂ) →L[ℂ] ℂ) : Measure K :=
  continuousMapRieszMeasure (PositiveLinearMap.mk₀ (continuousMapComplexModulus φ).toLinearMap
    ((operator_nonneg_iff _).mp (continuousMapComplexModulus_nonneg φ)))

instance continuousMapComplexModulusMeasure_finite (φ : C(K, ℂ) →L[ℂ] ℂ) :
    IsFiniteMeasure (continuousMapComplexModulusMeasure φ) := by
  unfold continuousMapComplexModulusMeasure
  infer_instance

instance continuousMapComplexModulusMeasure_regular (φ : C(K, ℂ) →L[ℂ] ℂ) :
    (continuousMapComplexModulusMeasure φ).Regular := by
  unfold continuousMapComplexModulusMeasure
  infer_instance

theorem continuousMapComplexModulusMeasure_mass (φ : C(K, ℂ) →L[ℂ] ℂ) :
    (continuousMapComplexModulusMeasure φ).real univ = ‖φ‖ := by
  rw [continuousMapComplexModulusMeasure, continuousMapRieszMeasure_mass]
  exact (norm_positive_continuousMapDual _ (continuousMapComplexModulus_nonneg φ)).symm.trans
    (norm_continuousMapComplexModulus φ)

theorem exists_continuousMap_complex_open_modulus_test (φ : C(K, ℂ) →L[ℂ] ℂ)
    {U : Set K} (hU : IsOpen U) {r : ℝ}
    (hr : r < (continuousMapComplexModulusMeasure φ).real U) :
    ∃ g : C(K, ℂ), ‖g‖ ≤ 1 ∧ (∀ x ∉ U, g x = 0) ∧ r < ‖φ g‖ := by
  obtain ⟨f, hf, hfs, hfr⟩ := exists_continuousMap_riesz_open_test _ hU hr
  obtain ⟨g, hg, hgr⟩ := exists_continuousMap_complex_modulus_test φ
    (show 0 ≤ f from fun x => (hf x).1) hfr
  refine ⟨g, (ContinuousMap.norm_le _ zero_le_one).mpr (fun x => (hg x).trans (hf x).2),
    ?_, hgr⟩
  intro x hx
  apply norm_eq_zero.mp
  exact le_antisymm ((hg x).trans_eq (hfs x hx)) (norm_nonneg _)

end ThesisCommon
