import JLMS.CZeroTools

/-!
# Real and imaginary parts of C₀ functions

Scalar decomposition respects continuity, vanishing at infinity, and the
supremum norm. These maps transport the real Riesz representation to both
scalar fields without imposing extra topological assumptions on K.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]

def ofRealCZero (f : CZero ℝ K) : CZero 𝕜 K where
  toFun x := (f x : 𝕜)
  continuous_toFun := RCLike.ofRealCLM.continuous.comp f.continuous_toFun
  zero_at_infty' := by
    simpa using (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.tendsto 0 |>.comp f.zero_at_infty'

@[simp] theorem ofRealCZero_apply (f : CZero ℝ K) (x : K) :
    ofRealCZero (𝕜 := 𝕜) f x = (f x : 𝕜) := rfl

theorem norm_ofRealCZero (f : CZero ℝ K) : ‖ofRealCZero (𝕜 := 𝕜) f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro x
    change ‖(f x : 𝕜)‖ ≤ ‖f‖
    simpa only [RCLike.norm_ofReal, ← Real.norm_eq_abs] using norm_CZero_apply_le f x
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg (ofRealCZero (𝕜 := 𝕜) f))).mpr
    intro x
    simpa only [ofRealCZero_apply, RCLike.norm_ofReal, ← Real.norm_eq_abs]
      using norm_CZero_apply_le (ofRealCZero (𝕜 := 𝕜) f) x

/-- Inclusion of real-valued functions, as a real continuous linear map. -/
def ofRealCZeroCLM : CZero ℝ K →L[ℝ] CZero 𝕜 K :=
  ({ toFun := ofRealCZero
     map_add' f g := by ext x; exact RCLike.ofReal_add _ _
     map_smul' c f := by
       ext x
       change ((c * f x : ℝ) : 𝕜) = c • (f x : 𝕜)
       rw [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul] } :
      CZero ℝ K →ₗ[ℝ] CZero 𝕜 K).mkContinuous 1
        (fun f : CZero ℝ K => by simp [norm_ofRealCZero (𝕜 := 𝕜)])

@[simp] theorem ofRealCZeroCLM_apply (f : CZero ℝ K) :
    ofRealCZeroCLM (𝕜 := 𝕜) f = ofRealCZero f := rfl

def realPartCZero (f : CZero 𝕜 K) : CZero ℝ K where
  toFun x := RCLike.re (f x)
  continuous_toFun := RCLike.reCLM.continuous.comp f.continuous_toFun
  zero_at_infty' := by
    simpa using RCLike.reCLM.continuous.tendsto 0 |>.comp f.zero_at_infty'

def imaginaryPartCZero (f : CZero 𝕜 K) : CZero ℝ K where
  toFun x := RCLike.im (f x)
  continuous_toFun := RCLike.imCLM.continuous.comp f.continuous_toFun
  zero_at_infty' := by
    simpa using RCLike.imCLM.continuous.tendsto 0 |>.comp f.zero_at_infty'

theorem real_imaginary_decomposition (f : CZero 𝕜 K) :
    ofRealCZero (𝕜 := 𝕜) (realPartCZero f) + (RCLike.I : 𝕜) •
      ofRealCZero (𝕜 := 𝕜) (imaginaryPartCZero f) = f := by
  ext x
  change (RCLike.re (f x) : 𝕜) + RCLike.I * (RCLike.im (f x) : 𝕜) = f x
  rw [mul_comm]
  exact RCLike.re_add_im (f x)

end JLMS
