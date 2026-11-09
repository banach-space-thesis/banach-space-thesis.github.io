import LindenstraussRetraction.Definitions
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic.Linarith

/-! The dependent c₀-sum as a closed subspace of the bounded ℓ∞-sum. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace LindenstraussRetraction

universe u v
variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]

/-- The bounded families whose coordinate norms tend to zero. -/
def c0SumSubmodule : Submodule 𝕜 (lp E ∞) where
  carrier := {x | Tendsto (fun n => ‖x n‖) atTop (𝓝 0)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change Tendsto (fun n => ‖x n + y n‖) atTop (𝓝 0)
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => norm_add_le _ _)
    simpa only [zero_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    change Tendsto (fun n => ‖c • x n‖) atTop (𝓝 0)
    simp only [norm_smul]
    simpa only [mul_zero] using tendsto_const_nhds.mul hx

/-- `(⊕ E_n)_c₀`, with its inherited supremum norm. -/
abbrev C0Sum : Type u := c0SumSubmodule 𝕜 E

theorem c0SumSubmodule_isClosed : IsClosed (c0SumSubmodule 𝕜 E : Set (lp E ∞)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun n => ‖x n‖) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := (Metric.mem_closure_iff.1 hx) (ε/2) (half_pos hε)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hy) (ε/2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  simp only [dist_zero_right, norm_norm]
  have hc : ‖x n - y n‖ ≤ ‖x-y‖ := by
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (x-y) n
  have hn' : ‖y n‖ < ε/2 := by simpa only [dist_zero_right, norm_norm] using hN n hn
  have hxy' : ‖x-y‖ < ε/2 := by simpa only [dist_eq_norm] using hxy
  calc
    ‖x n‖ = ‖(x n-y n)+y n‖ := by rw [sub_add_cancel]
    _ ≤ ‖x n-y n‖ + ‖y n‖ := norm_add_le _ _
    _ < ε := by linarith

instance c0Sum_complete [∀ n, CompleteSpace (E n)] : CompleteSpace (C0Sum 𝕜 E) :=
  (c0SumSubmodule_isClosed 𝕜 E).completeSpace_coe

theorem c0Sum_norm_coordinate_le (x : C0Sum 𝕜 E) (n : ℕ) : ‖x.val n‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x.val n

theorem c0Sum_norm_le {x : C0Sum 𝕜 E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, ‖x.val n‖ ≤ C) : ‖x‖ ≤ C :=
  lp.norm_le_of_forall_le hC h

theorem c0Sum_tendsto_zero (x : C0Sum 𝕜 E) :
    Tendsto (fun n => ‖x.val n‖) atTop (𝓝 0) := x.property

end LindenstraussRetraction
