import ThesisCommon.Analysis.PositiveRieszDisjoint
import ThesisCommon.Analysis.MeasureDensityL1
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! The concrete density map from L1 of a finite Borel measure into C(K)*.
For positive real densities the norm is preserved. Radon--Nikodym densities
recover actual absolutely continuous positive functionals; no representation
or principal-band isomorphism is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K 𝕜 : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [RCLike 𝕜]
variable (μ : Measure K) [IsFiniteMeasure μ]

def continuousMapL1Density : Lp 𝕜 1 μ →L[𝕜] (C(K, 𝕜) →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.precompR C(K, 𝕜)
    ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ 1 ∞)).flip
      (ContinuousMap.toLp ∞ μ 𝕜)

theorem continuousMapL1Density_apply (f : Lp 𝕜 1 μ) (g : C(K, 𝕜)) :
    continuousMapL1Density (𝕜 := 𝕜) μ f g = ∫ x, f x * g x ∂μ := by
  change (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ 1 ∞ f
    (ContinuousMap.toLp ∞ μ 𝕜 g) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := ∞) μ g] with x hx
  simp only [ContinuousLinearMap.mul_apply', hx]

theorem continuousMap_toLinfty_norm_le (g : C(K, 𝕜)) :
    ‖ContinuousMap.toLp ∞ μ 𝕜 g‖ ≤ ‖g‖ := by
  have h := ContinuousMap.toLp_norm_le (𝕜 := 𝕜) (E := 𝕜) (p := ∞) μ
  simp only [ENNReal.toReal_top, inv_zero, Real.rpow_zero] at h
  exact (ContinuousLinearMap.le_opNorm _ g).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg g))

theorem continuousMapL1Density_bound (f : Lp 𝕜 1 μ) (g : C(K, 𝕜)) :
    ‖continuousMapL1Density (𝕜 := 𝕜) μ f g‖ ≤ ‖f‖ * ‖g‖ := by
  let B := ContinuousLinearMap.mul 𝕜 𝕜
  let h := ContinuousMap.toLp ∞ μ 𝕜 g
  change ‖B.lpPairing μ 1 ∞ f h‖ ≤ _
  have he : B.lpPairing μ 1 ∞ f h = L1.integral (B.holder 1 f h) := by
    rw [B.lpPairing_eq_integral, L1.integral_eq_integral]
    exact (integral_congr_ae (B.coeFn_holder f h)).symm
  rw [he]
  calc
    _ ≤ ‖B.holder 1 f h‖ := L1.norm_integral_le _
    _ ≤ ‖B‖ * ‖f‖ * ‖h‖ := B.norm_holder_apply_apply_le f h
    _ ≤ 1 * ‖f‖ * ‖g‖ := by
      gcongr
      · exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
      · exact continuousMap_toLinfty_norm_le μ g
    _ = _ := by rw [one_mul]

theorem norm_continuousMapL1Density_le (f : Lp 𝕜 1 μ) :
    ‖continuousMapL1Density (𝕜 := 𝕜) μ f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (continuousMapL1Density_bound μ f)

theorem continuousMapL1Density_nonneg (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    0 ≤ continuousMapL1Density (𝕜 := ℝ) μ f := by
  apply (operator_nonneg_iff _).mpr
  intro g hg
  rw [continuousMapL1Density_apply]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with x hx
  exact mul_nonneg hx (hg x)

theorem continuousMapL1Density_norm_of_nonneg (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    ‖continuousMapL1Density (𝕜 := ℝ) μ f‖ = ‖f‖ := by
  rw [norm_positive_continuousMapDual _ (continuousMapL1Density_nonneg μ f hf),
    continuousMapL1Density_apply, L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with x hx
  simp only [ContinuousMap.one_apply, mul_one, Real.norm_of_nonneg hx]

variable [T2Space K]

theorem continuousMapL1Density_measureDensity (ν : Measure K) [IsFiniteMeasure ν]
    (hν : ν ≪ μ) :
    continuousMapL1Density (𝕜 := ℝ) μ (measureDensityL1 ν μ) = continuousMapIntegralCLM ν := by
  ext g
  rw [continuousMapL1Density_apply]
  change (∫ x, measureDensityL1 ν μ x * g x ∂μ) = ∫ x, g x ∂ν
  calc
    _ = ∫ x, (ν.rnDeriv μ x).toReal • g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [measureDensityL1_coe ν μ] with x hx
      simp only [hx, smul_eq_mul]
    _ = _ := integral_rnDeriv_smul hν

theorem positiveContinuousMap_density_representation
    (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ)
    (hAC : positiveContinuousMapRiesz φ hφ ≪ μ) :
    ∃ f : Lp ℝ 1 μ, 0 ≤ f ∧ continuousMapL1Density (𝕜 := ℝ) μ f = φ ∧ ‖f‖ = ‖φ‖ := by
  refine ⟨measureDensityL1 (positiveContinuousMapRiesz φ hφ) μ,
    measureDensityL1_nonneg _ _, ?_, ?_⟩
  · rw [continuousMapL1Density_measureDensity μ _ hAC,
      continuousMapIntegralCLM_positiveContinuousMapRiesz]
  · rw [norm_measureDensityL1 _ _ hAC]
    exact positiveContinuousMapRiesz_mass_norm φ hφ

end ThesisCommon
