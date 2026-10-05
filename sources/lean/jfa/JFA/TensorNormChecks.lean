import JFA.TensorProducts
import Mathlib.Analysis.Normed.Module.Dual

/-! Small checked facts tying the concrete tensor-space definition to the
paper's crossnorm. These do not prove any of the paper's five main results. -/

noncomputable section
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Hahn-Banach gives the full product norm on elementary tensors. -/
theorem norm_injectivePure (e : E) (x : X) :
    ‖injectivePure 𝕜 E X e x‖ = ‖e‖ * ‖x‖ := by
  change ‖(ContinuousLinearMap.apply 𝕜 𝕜 e).smulRight x‖ = _
  rw [ContinuousLinearMap.norm_smulRight_apply]
  have h : ‖ContinuousLinearMap.apply 𝕜 𝕜 e‖ = ‖e‖ :=
    (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map e
  rw [h]

/-- The operator norm is precisely the least constant controlling products of
dual evaluations. This characterizes the paper's epsilon norm on finite sums. -/
theorem dualOperator_norm_le_iff (A : DualOperators 𝕜 E X) (r : ℝ) (hr : 0 ≤ r) :
    ‖A‖ ≤ r ↔ ∀ (φ : E →L[𝕜] 𝕜) (ψ : X →L[𝕜] 𝕜),
      ‖ψ (A φ)‖ ≤ (r * ‖φ‖) * ‖ψ‖ := by
  constructor
  · intro h φ ψ
    calc
      ‖ψ (A φ)‖ ≤ ‖ψ‖ * ‖A φ‖ := ψ.le_opNorm _
      _ ≤ ‖ψ‖ * (r * ‖φ‖) := mul_le_mul_of_nonneg_left
        ((A.le_opNorm φ).trans (mul_le_mul_of_nonneg_right h (norm_nonneg φ)))
        (norm_nonneg ψ)
      _ = (r * ‖φ‖) * ‖ψ‖ := mul_comm _ _
  · intro h
    apply ContinuousLinearMap.opNorm_le_bound A hr
    intro φ
    exact NormedSpace.norm_le_dual_bound 𝕜 (A φ) (mul_nonneg hr (norm_nonneg φ)) (h φ)

end JFA
