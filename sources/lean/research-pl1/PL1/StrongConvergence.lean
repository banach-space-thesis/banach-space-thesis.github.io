import PL1.Definitions
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Strong convergence from a dense family

Uniformly bounded continuous linear operators converge everywhere if they
converge on a family with dense linear span. This supplies the density step
from Walsh multiplier convergence to strong convergence on actual L1.
-/

noncomputable section
open Filter
open scoped Topology NNReal

namespace PL1

variable {𝕜 E F ι β : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def convergenceSubmodule (T : β → E →L[𝕜] F) (T₀ : E →L[𝕜] F) (l : Filter β) :
    Submodule 𝕜 E where
  carrier := {x | Tendsto (fun b => T b x) l (𝓝 (T₀ x))}
  zero_mem' := by simpa using (tendsto_const_nhds (x := (0 : F)) (f := l))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq, map_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_ofPred_eq, map_smul] using hx.const_smul c

theorem isClosed_convergenceSubmodule (T : β → E →L[𝕜] F) (T₀ : E →L[𝕜] F)
    (l : Filter β) (C : ℝ≥0) (hT : ∀ b, ‖T b‖ ≤ C) :
    IsClosed (convergenceSubmodule T T₀ l : Set E) := by
  have hLip (b : β) : LipschitzWith C (T b) :=
    (T b).lipschitzWith.weaken (show ‖T b‖₊ ≤ C from hT b)
  exact (LipschitzWith.uniformEquicontinuous (fun b => T b) C hLip).equicontinuous
    |>.isClosed_setOfPred_tendsto T₀.continuous

/-- The complete density argument for a uniformly bounded operator family. -/
theorem tendsto_apply_of_dense_span (v : ι → E)
    (hv : Dense (Submodule.span 𝕜 (Set.range v) : Set E))
    (T : β → E →L[𝕜] F) (T₀ : E →L[𝕜] F) (l : Filter β)
    (C : ℝ≥0) (hT : ∀ b, ‖T b‖ ≤ C)
    (h : ∀ i, Tendsto (fun b => T b (v i)) l (𝓝 (T₀ (v i)))) (x : E) :
    Tendsto (fun b => T b x) l (𝓝 (T₀ x)) := by
  have hs : Submodule.span 𝕜 (Set.range v) ≤ convergenceSubmodule T T₀ l := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact h i
  have hcl := isClosed_convergenceSubmodule T T₀ l C hT
  exact hcl.closure_subset_iff.mpr hs (hv x)

end PL1
