import ThesisCommon.Analysis.ContinuousMapComplexRiesz
import Mathlib.Analysis.Normed.Module.RCLike.Extend

/-! Actual real coordinates and isometric complexification of the dual of
C(K). The complexification is obtained from the real part by the canonical
norm-preserving extension of real functionals on a complex normed space. -/
noncomputable section
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def continuousMapReCLM : C(K, ℂ) →L[ℝ] C(K, ℝ) :=
  LinearMap.mkContinuous
    { toFun := continuousMapRealPart
      map_add' := fun f g => by ext t; exact Complex.add_re _ _
      map_smul' := fun c f => by ext t; simp [continuousMapRealPart] }
    1 (fun f => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro t
      exact (Complex.abs_re_le_norm _).trans (f.norm_coe_le_norm t))

@[simp] theorem continuousMapReCLM_ofReal (f : C(K, ℝ)) :
    continuousMapReCLM (continuousMapOfReal f) = f := by ext t; rfl

theorem continuousMapReCLM_I (f : C(K, ℂ)) :
    continuousMapReCLM (Complex.I • f) = -continuousMapImagPart f := by
  ext t
  change (Complex.I * f t).re = -(f t).im
  simp

def continuousMapDualComplexify (ψ : C(K, ℝ) →L[ℝ] ℝ) : C(K, ℂ) →L[ℂ] ℂ :=
  (ψ.comp continuousMapReCLM).extendTo𝕜'

theorem continuousMapDualComplexify_apply (ψ : C(K, ℝ) →L[ℝ] ℝ) (f : C(K, ℂ)) :
    continuousMapDualComplexify ψ f = (ψ (continuousMapRealPart f) : ℂ) +
      Complex.I * (ψ (continuousMapImagPart f) : ℂ) := by
  rw [continuousMapDualComplexify, ContinuousLinearMap.extendTo𝕜'_apply]
  change (ψ (continuousMapReCLM f) : ℂ) - Complex.I *
    (ψ (continuousMapReCLM (Complex.I • f)) : ℂ) = _
  simp only [ContinuousLinearMap.comp_apply, continuousMapReCLM_I, map_neg,
    Complex.ofReal_neg, mul_neg, sub_neg_eq_add]
  rfl

@[simp] theorem continuousMapDualComplexify_ofReal (ψ : C(K, ℝ) →L[ℝ] ℝ) (f : C(K, ℝ)) :
    continuousMapDualComplexify ψ (continuousMapOfReal f) = (ψ f : ℂ) := by
  rw [continuousMapDualComplexify_apply]
  have hr : continuousMapRealPart (continuousMapOfReal (𝕜 := ℂ) f) = f := by ext t; rfl
  have hi : continuousMapImagPart (continuousMapOfReal (𝕜 := ℂ) f) = 0 := by ext t; rfl
  rw [hr, hi, map_zero, Complex.ofReal_zero, mul_zero, add_zero]

theorem norm_continuousMapDualComplexify (ψ : C(K, ℝ) →L[ℝ] ℝ) :
    ‖continuousMapDualComplexify ψ‖ = ‖ψ‖ := by
  rw [continuousMapDualComplexify, ContinuousLinearMap.norm_extendTo𝕜']
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ψ)
    intro f
    apply (ψ.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg ψ)
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro t
    exact (Complex.abs_re_le_norm _).trans (f.norm_coe_le_norm t)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    simpa only [ContinuousLinearMap.comp_apply, continuousMapReCLM_ofReal,
      norm_continuousMapOfReal_apply] using
      (ψ.comp continuousMapReCLM).le_opNorm (continuousMapOfReal (𝕜 := ℂ) f)

theorem continuousMap_complex_dual_ext {φ ψ : C(K, ℂ) →L[ℂ] ℂ}
    (h : ∀ f : C(K, ℝ), φ (continuousMapOfReal f) = ψ (continuousMapOfReal f)) : φ = ψ := by
  apply ContinuousLinearMap.ext
  intro f
  rw [← continuousMap_re_add_im f, map_add, map_add, map_smul, map_smul, h, h]

def continuousMapDualRe : (C(K, ℂ) →L[ℂ] ℂ) →L[ℝ] (C(K, ℝ) →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := continuousMapFunctionalRe (K := K) (𝕜 := ℂ)
      map_add' := fun φ ψ => by ext f; exact Complex.add_re _ _
      map_smul' := fun c φ => by ext f; simp [continuousMapFunctionalRe] }
    1 (fun φ => by simpa only [one_mul] using norm_continuousMapFunctionalRe_le φ)

def continuousMapDualIm : (C(K, ℂ) →L[ℂ] ℂ) →L[ℝ] (C(K, ℝ) →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := continuousMapFunctionalIm (K := K) (𝕜 := ℂ)
      map_add' := fun φ ψ => by ext f; exact Complex.add_im _ _
      map_smul' := fun c φ => by ext f; simp [continuousMapFunctionalIm] }
    1 (fun φ => by simpa only [one_mul] using norm_continuousMapFunctionalIm_le φ)

def continuousMapDualOfReal : (C(K, ℝ) →L[ℝ] ℝ) →L[ℝ] (C(K, ℂ) →L[ℂ] ℂ) :=
  LinearMap.mkContinuous
    { toFun := continuousMapDualComplexify (K := K)
      map_add' := fun φ ψ => by
        apply continuousMap_complex_dual_ext
        intro f
        simp
      map_smul' := fun c φ => by
        apply continuousMap_complex_dual_ext
        intro f
        simp }
    1 (fun φ => by simpa only [one_mul] using (norm_continuousMapDualComplexify φ).le)

@[simp] theorem continuousMapDualRe_ofReal (ψ : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapDualRe (continuousMapDualOfReal ψ) = ψ := by
  apply ContinuousLinearMap.ext
  intro f
  change (continuousMapDualComplexify ψ (continuousMapOfReal f)).re = ψ f
  rw [continuousMapDualComplexify_ofReal]
  rfl

@[simp] theorem continuousMapDualIm_ofReal (ψ : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapDualIm (continuousMapDualOfReal ψ) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change (continuousMapDualComplexify ψ (continuousMapOfReal f)).im = 0
  rw [continuousMapDualComplexify_ofReal]
  rfl

theorem continuousMapDual_decomposition (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapDualOfReal (continuousMapDualRe φ) +
      Complex.I • continuousMapDualOfReal (continuousMapDualIm φ) = φ := by
  apply continuousMap_complex_dual_ext
  intro f
  change continuousMapDualComplexify (continuousMapDualRe φ) (continuousMapOfReal f) +
    Complex.I * continuousMapDualComplexify (continuousMapDualIm φ) (continuousMapOfReal f) = _
  rw [continuousMapDualComplexify_ofReal, continuousMapDualComplexify_ofReal]
  change ((φ (continuousMapOfReal f)).re : ℂ) + Complex.I * ((φ (continuousMapOfReal f)).im : ℂ) = _
  rw [mul_comm, Complex.re_add_im]

theorem continuousMapDualRe_smul (a : ℂ) (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapDualRe (a • φ) = a.re • continuousMapDualRe φ - a.im • continuousMapDualIm φ := by
  apply ContinuousLinearMap.ext
  intro f
  exact Complex.mul_re _ _

theorem continuousMapDualIm_smul (a : ℂ) (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapDualIm (a • φ) = a.re • continuousMapDualIm φ + a.im • continuousMapDualRe φ := by
  apply ContinuousLinearMap.ext
  intro f
  exact Complex.mul_im _ _

theorem norm_continuousMapDualOfReal (ψ : C(K, ℝ) →L[ℝ] ℝ) :
    ‖continuousMapDualOfReal ψ‖ = ‖ψ‖ := norm_continuousMapDualComplexify ψ

end ThesisCommon
