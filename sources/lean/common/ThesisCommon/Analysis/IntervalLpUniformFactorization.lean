import ThesisCommon.Analysis.IntervalLpScalarCompression
import ThesisCommon.Analysis.ScalarCompressionCriterion

/-! Uniform primary factorisation for actual interval Lp, over real and
complex scalars and every finite Banach exponent. The mean-zero space
has CPFP constant four; mutual complemented embeddings transfer UPFP to
the full interval Lp space. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace ThesisCommon
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
instance intervalLpMeanZero_completeSpace (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    CompleteSpace (IntervalLpMeanZero 𝕜 p) :=
  (ContinuousLinearMap.isClosed_ker (lpHaarIntegral (𝕜 := 𝕜) (p := p.val)
    (μ := volume.restrict (Icc (0 : ℝ) 1)))).completeSpace_coe

variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem intervalLpMeanZero_scalar_compressions
    (T : IntervalLpMeanZero 𝕜 p →L[𝕜] IntervalLpMeanZero 𝕜 p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : IntervalLpMeanZero 𝕜 p →L[𝕜] IntervalLpMeanZero 𝕜 p, ∃ c : 𝕜,
      A.comp B = ContinuousLinearMap.id 𝕜 (IntervalLpMeanZero 𝕜 p) ∧
      ‖A‖ * ‖B‖ ≤ 1 ∧
      ‖((A.comp T).comp B) - c • ContinuousLinearMap.id 𝕜 (IntervalLpMeanZero 𝕜 p)‖ < ε := by
  let P := intervalLpMeanZeroProjection 𝕜 p
  let U := (intervalLpMeanZeroSubmodule 𝕜 p).subtypeL.comp (T.comp P)
  have hUmean (f : IntervalLp 𝕜 p) : lpHaarIntegral (U f) = 0 := (T (P f)).property
  have hUconst : U (lpHaarRawVector 𝕜 p none) = 0 := by
    have hP : P (lpHaarRawVector 𝕜 p none) = 0 := by
      apply Subtype.ext
      change lpHaarRawVector 𝕜 p none - lpHaarIntegral (lpHaarRawVector 𝕜 p none) •
        lpHaarRawVector 𝕜 p none = 0
      rw [lpHaarRawVector, lpHaarIntegral_const, one_smul, sub_self]
    simp only [U, ContinuousLinearMap.comp_apply, hP, map_zero]
  obtain ⟨A, B, c, hA, hB, hAB, hmA, hmB, hscalar⟩ :=
    intervalLp_scalar_compression_meanZero 𝕜 p hp U hUmean hUconst hε
  have hAz (f : IntervalLp 𝕜 p) (hf : lpHaarIntegral f = 0) : lpHaarIntegral (A f) = 0 :=
    (hmA f).trans hf
  have hBz (f : IntervalLp 𝕜 p) (hf : lpHaarIntegral f = 0) : lpHaarIntegral (B f) = 0 :=
    (hmB f).trans hf
  let Ar := intervalLpMeanZeroRestrict 𝕜 p A hAz
  let Br := intervalLpMeanZeroRestrict 𝕜 p B hBz
  have hAr : ‖Ar‖ ≤ 1 := (norm_intervalLpMeanZeroRestrict_le 𝕜 p A hAz).trans hA
  have hBr : ‖Br‖ ≤ 1 := (norm_intervalLpMeanZeroRestrict_le 𝕜 p B hBz).trans hB
  refine ⟨Ar, Br, c, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    change A (B f.val) = f.val
    exact congrArg (fun S : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p => S f.val) hAB
  · nlinarith [norm_nonneg Ar, norm_nonneg Br]
  · have he (f : IntervalLpMeanZero 𝕜 p) :
        ‖(((Ar.comp T).comp Br) - c • ContinuousLinearMap.id 𝕜 (IntervalLpMeanZero 𝕜 p)) f‖ ≤
          (3 * ε / 4) * ‖f‖ := by
      have hP : P (B f.val) = Br f := by
        apply Subtype.ext
        have hf : lpHaarIntegral f.val = 0 := f.property
        change B f.val - lpHaarIntegral (B f.val) • lpHaarRawVector 𝕜 p none = B f.val
        rw [hmB, hf, zero_smul, sub_zero]
      have hU : U (B f.val) = (T (Br f)).val := by
        change (T (P (B f.val))).val = _
        rw [hP]
      have h := hscalar f.val f.property
      change ‖A (U (B f.val)) - c • f.val‖ ≤ (3 * ε / 4) * ‖f.val‖ at h
      rw [hU] at h
      exact h
    have hnorm := ContinuousLinearMap.opNorm_le_bound
      (((Ar.comp T).comp Br) - c • ContinuousLinearMap.id 𝕜 (IntervalLpMeanZero 𝕜 p))
      (by positivity : 0 ≤ 3 * ε / 4) he
    exact hnorm.trans_lt (by linarith)

include hp in
theorem intervalLpMeanZero_hasCPFP_four : HasCPFP 𝕜 (IntervalLpMeanZero 𝕜 p) 4 := by
  convert hasCPFP_of_scalar_compressions (C := 1)
    (fun T ε hε => intervalLpMeanZero_scalar_compressions 𝕜 p hp T hε) using 1 <;> norm_num

include hp in
theorem intervalLpMeanZero_hasUPFP : HasUPFP 𝕜 (IntervalLpMeanZero 𝕜 p) :=
  ⟨4, by norm_num, intervalLpMeanZero_hasCPFP_four 𝕜 p hp⟩

theorem intervalLp_hasUPFP (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞) :
    HasUPFP 𝕜 (IntervalLp 𝕜 p) :=
  intervalLp_hasUPFP_of_meanZero 𝕜 p hp (intervalLpMeanZero_hasUPFP 𝕜 p hp)

end ThesisCommon
