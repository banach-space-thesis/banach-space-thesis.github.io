import ThesisCommon.Analysis.LpHaarSchauderBasis
import ThesisCommon.Analysis.IntervalLpFunctionSelfSimilarity
import ThesisCommon.Analysis.SelfSimilarKernelRetract

/-! The actual closed mean-zero subspace of interval Lp and the two
complemented embeddings needed to transfer its uniform factorisations. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

def intervalLpMeanZeroSubmodule (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    Submodule 𝕜 (IntervalLp 𝕜 p) :=
  LinearMap.ker (lpHaarIntegral (𝕜 := 𝕜) (p := p.val)
    (μ := volume.restrict (Icc (0 : ℝ) 1))).toLinearMap

abbrev IntervalLpMeanZero (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :=
  intervalLpMeanZeroSubmodule 𝕜 p

def intervalLpMeanZeroProjection (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    IntervalLp 𝕜 p →L[𝕜] IntervalLpMeanZero 𝕜 p :=
  (ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) -
    (lpHaarIntegral (𝕜 := 𝕜) (p := p.val)).smulRight (lpHaarRawVector 𝕜 p none)).codRestrict
      (intervalLpMeanZeroSubmodule 𝕜 p) (fun x => by
        change lpHaarIntegral (x - lpHaarIntegral x • lpHaarRawVector 𝕜 p none) = 0
        rw [map_sub, map_smul]
        change lpHaarIntegral x - lpHaarIntegral x •
          lpHaarIntegral (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)) = 0
        rw [lpHaarIntegral_const]
        simp)

theorem intervalLpMeanZeroProjection_retract (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    (intervalLpMeanZeroProjection 𝕜 p).comp (intervalLpMeanZeroSubmodule 𝕜 p).subtypeL =
      ContinuousLinearMap.id 𝕜 (IntervalLpMeanZero 𝕜 p) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  have hx : lpHaarIntegral x.val = 0 := x.property
  change x.val - lpHaarIntegral x.val • lpHaarRawVector 𝕜 p none = x.val
  simp [hx]

theorem intervalLpMeanZero_contains_retract (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (hp : p.val ≠ ∞) :
    ∃ A : IntervalLpMeanZero 𝕜 p →L[𝕜] IntervalLp 𝕜 p,
      ∃ B : IntervalLp 𝕜 p →L[𝕜] IntervalLpMeanZero 𝕜 p,
        A.comp B = ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) :=
  selfSimilar_kernel_retract p (intervalLpFunctionSelfSimilarity 𝕜 p hp).toContinuousLinearEquiv
    lpHaarIntegral

/-- The transfer is proved for the manuscript's actual interval Lp space.
The sole input is UPFP of its actual mean-zero subspace. -/
theorem intervalLp_hasUPFP_of_meanZero (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (h : HasUPFP 𝕜 (IntervalLpMeanZero 𝕜 p)) : HasUPFP 𝕜 (IntervalLp 𝕜 p) := by
  obtain ⟨A, B, hAB⟩ := intervalLpMeanZero_contains_retract 𝕜 p hp
  exact h.of_mutual_retracts (intervalLpMeanZeroProjection 𝕜 p)
    (intervalLpMeanZeroSubmodule 𝕜 p).subtypeL
    (intervalLpMeanZeroProjection_retract 𝕜 p) A B hAB

end ThesisCommon
