import ThesisCommon.Analysis.InfinityQuotientScalarMaps
import ThesisCommon.Analysis.InfinityQuotientMasks

/-! Compatibility of real scalar maps with actual quotient localization.
This supplies the real/imaginary passage in the quotient compression argument. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 𝕝 : Type*} [RCLike 𝕜] [RCLike 𝕝]

theorem infinityQuotientScalarMap_mask (f : 𝕜 →L[ℝ] 𝕝)
    (A : Set ℕ) (x : InfinityCZeroQuotient 𝕜) :
    infinityQuotientScalarMap f (infinityQuotientMask (𝕜 := 𝕜) A x) =
      infinityQuotientMask (𝕜 := 𝕝) A (infinityQuotientScalarMap f x) := by
  classical
  apply infinityQuotient_ext
  intro U
  simp only [infinityQuotientEval_scalarMap, infinityQuotientEval_mask]
  by_cases hA : A ∈ U <;> simp [hA]

theorem infinityQuotientScalarMap_indicator (f : 𝕜 →L[ℝ] 𝕝) (A : Set ℕ) :
    infinityQuotientScalarMap f (infinityQuotientIndicator (𝕜 := 𝕜) A) =
      f 1 • infinityQuotientIndicator (𝕜 := 𝕝) A := by
  classical
  apply infinityQuotient_ext
  intro U
  simp only [infinityQuotientEval_scalarMap, infinityQuotientEval_indicator, map_smul]
  by_cases hA : A ∈ U <;> simp [hA]

@[simp] theorem infinityQuotientRe_indicator (A : Set ℕ) :
    infinityQuotientRe (𝕜 := 𝕜) (infinityQuotientIndicator (𝕜 := 𝕜) A) =
      infinityQuotientIndicator (𝕜 := ℝ) A := by
  simpa only [RCLike.reCLM_apply, RCLike.one_re, one_smul] using
    infinityQuotientScalarMap_indicator (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) A

@[simp] theorem infinityQuotientIm_indicator (A : Set ℕ) :
    infinityQuotientIm (𝕜 := 𝕜) (infinityQuotientIndicator (𝕜 := 𝕜) A) = 0 := by
  simpa only [RCLike.imCLM_apply, RCLike.one_im, zero_smul] using
    infinityQuotientScalarMap_indicator (RCLike.imCLM : 𝕜 →L[ℝ] ℝ) A

@[simp] theorem infinityQuotientOfReal_indicator (A : Set ℕ) :
    infinityQuotientOfReal (𝕜 := 𝕜) (infinityQuotientIndicator (𝕜 := ℝ) A) =
      infinityQuotientIndicator (𝕜 := 𝕜) A := by
  simpa only [RCLike.ofRealCLM_apply, map_one, one_smul] using
    infinityQuotientScalarMap_indicator (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) A

theorem infinityQuotient_reconstruction (x : InfinityCZeroQuotient 𝕜) :
    infinityQuotientOfReal (𝕜 := 𝕜) (infinityQuotientRe (𝕜 := 𝕜) x) +
      (RCLike.I : 𝕜) • infinityQuotientOfReal (𝕜 := 𝕜) (infinityQuotientIm (𝕜 := 𝕜) x) = x := by
  apply infinityQuotient_ext
  intro U
  simp only [map_add, map_smul, infinityQuotientEval_ofReal,
    infinityQuotientEval_re, infinityQuotientEval_im, smul_eq_mul]
  simpa only [mul_comm] using RCLike.re_add_im (infinityQuotientEval (𝕜 := 𝕜) U x)

end ThesisCommon
