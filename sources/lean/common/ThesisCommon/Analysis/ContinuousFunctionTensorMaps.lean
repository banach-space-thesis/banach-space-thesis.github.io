import ThesisCommon.Analysis.FreeNatUltrafilterTensorDensity

/-! Bounded coefficient insertion in continuous-function spaces, with the
actual supremum norm. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 K X : Type*} [RCLike 𝕜] [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def continuousFunctionScalarMultiply (f : C(K, 𝕜)) : X →L[𝕜] C(K, X) :=
  LinearMap.mkContinuous
    { toFun := fun x => continuousFunctionTensor x f
      map_add' := fun x y => by ext U; exact smul_add (f U) x y
      map_smul' := fun c x => by ext U; exact smul_comm (f U) c x }
    ‖f‖ (fun x => by
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg f) (norm_nonneg x))).mpr
      intro U
      change ‖f U • x‖ ≤ ‖f‖ * ‖x‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm U) (norm_nonneg x))

@[simp] theorem continuousFunctionScalarMultiply_apply (f : C(K, 𝕜)) (x : X) (U : K) :
    continuousFunctionScalarMultiply f x U = f U • x := rfl

theorem norm_continuousFunctionScalarMultiply_le (f : C(K, 𝕜)) :
    ‖continuousFunctionScalarMultiply (X := X) f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

end ThesisCommon
