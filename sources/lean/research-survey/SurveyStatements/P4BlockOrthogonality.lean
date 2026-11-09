import SurveyStatements.P4FiniteDecomposition
import SurveyStatements.P4LpDualApproximation
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Disjoint finite blocks and actual square-summable truncations. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology
open scoped BigOperators ENNReal

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContractiveFiniteDecomposition

variable (D : ContractiveFiniteDecomposition 𝕜 E)

lemma blockProjection_comp_of_ne {n m : ℕ} (hnm : n ≠ m) :
    (D.blockProjection n).comp (D.blockProjection m) = 0 := by
  simp only [blockProjection, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, D.comp]
  rcases lt_or_gt_of_ne hnm with h | h
  · have h₁ : min (n + 1) (m + 1) = n + 1 := by omega
    have h₂ : min (n + 1) m = n + 1 := by omega
    have h₃ : min n (m + 1) = n := by omega
    have h₄ : min n m = n := by omega
    rw [h₁, h₂, h₃, h₄]
    abel
  · have h₁ : min (n + 1) (m + 1) = m + 1 := by omega
    have h₂ : min (n + 1) m = m := by omega
    have h₃ : min n (m + 1) = m + 1 := by omega
    have h₄ : min n m = m := by omega
    rw [h₁, h₂, h₃, h₄]
    abel

lemma coordinate_on_block (n : ℕ) (x : D.Block n) : D.coordinate n x.val = x := by
  apply Subtype.ext
  exact D.blockProjection_coordinate n x

lemma coordinate_on_other_block {n m : ℕ} (hnm : n ≠ m) (x : D.Block m) :
    D.coordinate n x.val = 0 := by
  obtain ⟨y, hy⟩ := x.property
  change D.blockProjection m y = x.val at hy
  apply Subtype.ext
  change D.blockProjection n x.val = 0
  rw [← hy]
  have h := congrArg (fun A : E →L[𝕜] E => A y) (D.blockProjection_comp_of_ne hnm)
  exact h

end ContractiveFiniteDecomposition

variable {H : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (H n)] [∀ n, NormedSpace 𝕜 (H n)]

theorem lp2_nat_truncation_tendsto (h : lp H 2) :
    Tendsto (fun N => lp2Projection (𝕜 := 𝕜) (Finset.range N) h) atTop (𝓝 h) := by
  have ht := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h).comp tendsto_finset_range
  simpa only [lp2Projection_apply] using ht

theorem lp2_norm_coordinate_tendsto_zero (h : lp H 2) :
    Tendsto (fun n => ‖h n‖) atTop (𝓝 0) := by
  have hs := (lp.memℓp h).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  have ht := hs.tendsto_atTop_zero
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

end SurveyStatements.P4
