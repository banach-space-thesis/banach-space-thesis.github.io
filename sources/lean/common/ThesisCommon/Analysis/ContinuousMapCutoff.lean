import ThesisCommon.Analysis.ContinuousMapPullback

/-! Multiplication by a continuous real cutoff in [0,1] is a contraction
on real or complex continuous-function spaces. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def continuousMapCutoff (φ : C(K, ℝ)) (hφ : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) :
    C(K, 𝕜) →L[𝕜] C(K, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun t => (φ t : 𝕜) * f t, by fun_prop⟩
      map_add' := by intro f g; ext t; exact mul_add _ _ _
      map_smul' := by intro a f; ext t; change (φ t : 𝕜) * (a * f t) = a * ((φ t : 𝕜) * f t); ring }
    1 (fun f => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro t
      change ‖(φ t : 𝕜) * f t‖ ≤ ‖f‖
      rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hφ t).1]
      exact (mul_le_mul_of_nonneg_right (hφ t).2 (norm_nonneg (f t))).trans
        (by simpa only [one_mul] using f.norm_coe_le_norm t))

@[simp] theorem continuousMapCutoff_apply (φ : C(K, ℝ)) (hφ) (f : C(K, 𝕜)) (t : K) :
    continuousMapCutoff φ hφ f t = (φ t : 𝕜) * f t := rfl

theorem norm_continuousMapCutoff_le (φ : C(K, ℝ)) (hφ) :
    ‖continuousMapCutoff (𝕜 := 𝕜) φ hφ‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon
