import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! The scalar limits of a bounded weakly Cauchy sequence form an actual
continuous bidual functional. The convergence hypotheses concern the
given vector sequence and are proved at each application. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def weakCauchyValue (u : ℕ → E)
    (hconv : ∀ φ : E →L[𝕜] 𝕜, ∃ a : 𝕜, Tendsto (fun n => φ (u n)) atTop (𝓝 a))
    (φ : E →L[𝕜] 𝕜) : 𝕜 := (hconv φ).choose

theorem weakCauchyValue_tendsto (u : ℕ → E)
    (hconv : ∀ φ : E →L[𝕜] 𝕜, ∃ a : 𝕜, Tendsto (fun n => φ (u n)) atTop (𝓝 a))
    (φ : E →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (u n)) atTop (𝓝 (weakCauchyValue u hconv φ)) :=
  (hconv φ).choose_spec

def weakCauchyLimitLinear (u : ℕ → E)
    (hconv : ∀ φ : E →L[𝕜] 𝕜, ∃ a : 𝕜, Tendsto (fun n => φ (u n)) atTop (𝓝 a)) :
    (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 where
  toFun := weakCauchyValue u hconv
  map_add' φ ψ := tendsto_nhds_unique (weakCauchyValue_tendsto u hconv (φ + ψ))
    ((weakCauchyValue_tendsto u hconv φ).add (weakCauchyValue_tendsto u hconv ψ))
  map_smul' a φ := tendsto_nhds_unique (weakCauchyValue_tendsto u hconv (a • φ))
    (tendsto_const_nhds.smul (weakCauchyValue_tendsto u hconv φ))

theorem weakCauchyValue_norm_le (u : ℕ → E)
    (hconv : ∀ φ : E →L[𝕜] 𝕜, ∃ a : 𝕜, Tendsto (fun n => φ (u n)) atTop (𝓝 a))
    {C : ℝ} (hbound : ∀ n, ‖u n‖ ≤ C) (φ : E →L[𝕜] 𝕜) :
    ‖weakCauchyValue u hconv φ‖ ≤ C * ‖φ‖ := by
  apply le_of_tendsto (weakCauchyValue_tendsto u hconv φ).norm
  apply Eventually.of_forall
  intro n
  exact ((φ.le_opNorm (u n)).trans
    (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg φ))).trans_eq (mul_comm _ _)

def boundedWeakCauchyBidual (u : ℕ → E)
    (hconv : ∀ φ : E →L[𝕜] 𝕜, ∃ a : 𝕜, Tendsto (fun n => φ (u n)) atTop (𝓝 a))
    {C : ℝ} (hbound : ∀ n, ‖u n‖ ≤ C) : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  (weakCauchyLimitLinear u hconv).mkContinuous C
    (weakCauchyValue_norm_le u hconv hbound)

theorem boundedWeakCauchyBidual_tendsto (u : ℕ → E)
    (hconv : ∀ φ : E →L[𝕜] 𝕜, ∃ a : 𝕜, Tendsto (fun n => φ (u n)) atTop (𝓝 a))
    {C : ℝ} (hbound : ∀ n, ‖u n‖ ≤ C) (φ : E →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (u n)) atTop (𝓝 (boundedWeakCauchyBidual u hconv hbound φ)) :=
  weakCauchyValue_tendsto u hconv φ

end ThesisCommon
