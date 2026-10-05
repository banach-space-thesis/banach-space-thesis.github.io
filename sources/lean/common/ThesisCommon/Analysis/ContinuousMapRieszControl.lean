import ThesisCommon.Analysis.ContinuousMapComplexRiesz

/-! Pointwise domination of the genuine representing vector measure. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {K 𝕜 : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [RCLike 𝕜]

theorem continuousMapRieszSigned_norm_le (μ : C(K, ℝ) →L[ℝ] ℝ) (s : Set K) :
    ‖continuousMapRieszSigned μ s‖ ≤
      (continuousMapRieszPositive μ).real s + (continuousMapRieszNegative μ).real s := by
  by_cases hs : MeasurableSet s
  · rw [continuousMapRieszSigned_apply μ hs]
    exact (norm_sub_le _ _).trans_eq (by rw [Real.norm_of_nonneg measureReal_nonneg,
      Real.norm_of_nonneg measureReal_nonneg])
  · rw [VectorMeasure.not_measurable _ hs, norm_zero]
    exact add_nonneg measureReal_nonneg measureReal_nonneg

theorem rclike_norm_I_le_one : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
  by_cases h : (RCLike.I : 𝕜) = 0
  · simp [h]
  · exact (RCLike.norm_I_of_ne_zero h).le

theorem continuousMapRieszVector_norm_le_control (μ : C(K, 𝕜) →L[𝕜] 𝕜) (s : Set K) :
    ‖continuousMapRieszVector μ s‖ ≤ (continuousMapRieszControl μ).real s := by
  rw [continuousMapRieszVector_apply]
  have hr := continuousMapRieszSigned_norm_le (continuousMapFunctionalRe μ) s
  have hi := continuousMapRieszSigned_norm_le (continuousMapFunctionalIm μ) s
  have hI : ‖(continuousMapRieszSigned (continuousMapFunctionalIm μ) s : 𝕜) * RCLike.I‖ ≤
      ‖continuousMapRieszSigned (continuousMapFunctionalIm μ) s‖ := by
    rw [norm_mul, RCLike.norm_ofReal]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (rclike_norm_I_le_one (𝕜 := 𝕜))
      (norm_nonneg (continuousMapRieszSigned (continuousMapFunctionalIm μ) s))
  have hn := (norm_add_le (continuousMapRieszSigned (continuousMapFunctionalRe μ) s : 𝕜)
    ((continuousMapRieszSigned (continuousMapFunctionalIm μ) s : 𝕜) * RCLike.I)).trans
      (add_le_add le_rfl hI)
  rw [RCLike.norm_ofReal] at hn
  unfold continuousMapRieszControl
  rw [measureReal_add_apply, measureReal_add_apply, measureReal_add_apply]
  exact hn.trans (add_le_add hr hi)

theorem continuousMapRieszVector_norm_le (μ : C(K, 𝕜) →L[𝕜] 𝕜) (s : Set K) :
    ‖continuousMapRieszVector μ s‖ ≤ 2 * ‖μ‖ :=
  (continuousMapRieszVector_norm_le_control μ s).trans
    ((measureReal_mono (Set.subset_univ s)).trans (continuousMapRieszControl_mass_le μ))

end ThesisCommon
