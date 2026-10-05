import ThesisCommon.Analysis.InfinityQuotientEvaluation
import ThesisCommon.Analysis.LpOperators

/-! Real-linear scalar maps on the genuine bounded-sequence quotient,
including real and imaginary parts and their free-ultrafilter evaluations. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 𝕝 : Type*} [RCLike 𝕜] [RCLike 𝕝]

def infinityScalarMap (f : 𝕜 →L[ℝ] 𝕝) :
    lp (fun _ : ℕ => 𝕜) ∞ →L[ℝ] lp (fun _ : ℕ => 𝕝) ∞ :=
  lpDiagonal ∞ (fun _ => f) ‖f‖ (norm_nonneg f) (fun _ => le_rfl)

@[simp] theorem infinityScalarMap_apply (f : 𝕜 →L[ℝ] 𝕝)
    (x : lp (fun _ : ℕ => 𝕜) ∞) (n : ℕ) : infinityScalarMap f x n = f (x n) := rfl

theorem norm_infinityScalarMap_le (f : 𝕜 →L[ℝ] 𝕝) : ‖infinityScalarMap f‖ ≤ ‖f‖ :=
  norm_lpDiagonal_le _ _ _ _

def infinityQuotientScalarMap (f : 𝕜 →L[ℝ] 𝕝) :
    InfinityCZeroQuotient 𝕜 →L[ℝ] InfinityCZeroQuotient 𝕝 :=
  quotientMapL ((scalarCZeroSubmodule 𝕜).restrictScalars ℝ)
    ((scalarCZeroSubmodule 𝕝).restrictScalars ℝ) (infinityScalarMap f) (by
      intro x hx
      change Tendsto (fun n => f (x n)) cofinite (𝓝 (0 : 𝕝))
      simpa only [map_zero] using (f.continuous.tendsto (0 : 𝕜)).comp hx)

@[simp] theorem infinityQuotientScalarMap_mk (f : 𝕜 →L[ℝ] 𝕝)
    (x : lp (fun _ : ℕ => 𝕜) ∞) :
    infinityQuotientScalarMap f (infinityQuotientMk (𝕜 := 𝕜) x) =
      infinityQuotientMk (𝕜 := 𝕝) (infinityScalarMap f x) := rfl

theorem norm_infinityQuotientScalarMap_le (f : 𝕜 →L[ℝ] 𝕝) :
    ‖infinityQuotientScalarMap f‖ ≤ ‖f‖ :=
  (norm_quotientMapL_le _ _ _ _).trans (norm_infinityScalarMap_le f)

theorem infinityQuotientEval_scalarMap (f : 𝕜 →L[ℝ] 𝕝)
    (U : FreeNatUltrafilter) (x : InfinityCZeroQuotient 𝕜) :
    infinityQuotientEval (𝕜 := 𝕝) U (infinityQuotientScalarMap f x) =
      f (infinityQuotientEval (𝕜 := 𝕜) U x) := by
  induction x using Quotient.inductionOn' with
  | h x =>
    change scalarUltralimit U.val (infinityScalarMap f x) = f (scalarUltralimit U.val x)
    apply scalarUltralimit_eq_of_tendsto
    exact (f.continuous.tendsto _).comp (scalarUltralimit_tendsto U.val x)

def infinityQuotientRe : InfinityCZeroQuotient 𝕜 →L[ℝ] InfinityCZeroQuotient ℝ :=
  infinityQuotientScalarMap RCLike.reCLM

def infinityQuotientIm : InfinityCZeroQuotient 𝕜 →L[ℝ] InfinityCZeroQuotient ℝ :=
  infinityQuotientScalarMap RCLike.imCLM

def infinityQuotientOfReal : InfinityCZeroQuotient ℝ →L[ℝ] InfinityCZeroQuotient 𝕜 :=
  infinityQuotientScalarMap RCLike.ofRealCLM

@[simp] theorem infinityQuotientEval_re (U : FreeNatUltrafilter)
    (x : InfinityCZeroQuotient 𝕜) :
    infinityQuotientEval (𝕜 := ℝ) U (infinityQuotientRe (𝕜 := 𝕜) x) =
      RCLike.re (infinityQuotientEval (𝕜 := 𝕜) U x) :=
  infinityQuotientEval_scalarMap RCLike.reCLM U x

@[simp] theorem infinityQuotientEval_im (U : FreeNatUltrafilter)
    (x : InfinityCZeroQuotient 𝕜) :
    infinityQuotientEval (𝕜 := ℝ) U (infinityQuotientIm (𝕜 := 𝕜) x) =
      RCLike.im (infinityQuotientEval (𝕜 := 𝕜) U x) :=
  infinityQuotientEval_scalarMap RCLike.imCLM U x

@[simp] theorem infinityQuotientEval_ofReal (U : FreeNatUltrafilter)
    (x : InfinityCZeroQuotient ℝ) :
    infinityQuotientEval (𝕜 := 𝕜) U (infinityQuotientOfReal (𝕜 := 𝕜) x) =
      (infinityQuotientEval (𝕜 := ℝ) U x : 𝕜) :=
  infinityQuotientEval_scalarMap RCLike.ofRealCLM U x

theorem infinityQuotient_re_im_ext {x y : InfinityCZeroQuotient 𝕜}
    (hre : infinityQuotientRe (𝕜 := 𝕜) x = infinityQuotientRe (𝕜 := 𝕜) y)
    (him : infinityQuotientIm (𝕜 := 𝕜) x = infinityQuotientIm (𝕜 := 𝕜) y) : x = y := by
  apply infinityQuotient_ext
  intro U
  apply RCLike.ext
  · simpa only [infinityQuotientEval_re] using
      congrArg (infinityQuotientEval (𝕜 := ℝ) U) hre
  · simpa only [infinityQuotientEval_im] using
      congrArg (infinityQuotientEval (𝕜 := ℝ) U) him

end ThesisCommon
