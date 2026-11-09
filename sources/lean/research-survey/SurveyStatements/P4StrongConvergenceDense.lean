import SurveyStatements.P4Definitions
import Mathlib.Tactic

/-! Uniformly bounded operators converge on every vector if they converge
on a norm-dense set, without any separability assumption. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter Topology

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem strong_tendsto_of_dense_set (S : ℕ → E →L[𝕜] F) (T : E →L[𝕜] F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ n, ‖S n‖ ≤ B)
    (D : Set E) (hdense : Dense D)
    (hD : ∀ y ∈ D, Tendsto (fun n => S n y) atTop (𝓝 (T y))) :
    ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (T x)) := by
  intro x
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let M : ℝ := B + ‖T‖ + 1
  have hM : 0 < M := by dsimp [M]; linarith [T.opNorm_nonneg]
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hdense x)
    (ε / (4 * M)) (div_pos hε (mul_pos (by norm_num) hM))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hD y hy) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm] at hxy ⊢
  have hsmall : (B + ‖T‖) * ‖x - y‖ < ε / 4 := by
    have hmul := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hM)).mp hxy
    dsimp [M] at hmul
    nlinarith [norm_nonneg (x - y)]
  have hn' := hN n hn
  rw [dist_eq_norm] at hn'
  have heq : S n x - T x = S n (x - y) + (S n y - T y) - T (x - y) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    ‖S n (x - y) + (S n y - T y) - T (x - y)‖ ≤
        ‖S n (x - y)‖ + ‖S n y - T y‖ + ‖T (x - y)‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ B * ‖x - y‖ + ‖S n y - T y‖ + ‖T‖ * ‖x - y‖ := by
      apply add_le_add
      · apply add_le_add_right
        exact ((S n).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
      · exact T.le_opNorm _
    _ = (B + ‖T‖) * ‖x - y‖ + ‖S n y - T y‖ := by ring
    _ < ε := by linarith

theorem strong_tendsto_of_dense_span (S : ℕ → E →L[𝕜] F) (T : E →L[𝕜] F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ n, ‖S n‖ ≤ B)
    (D : Set E) (hdense : Dense (Submodule.span 𝕜 D : Set E))
    (hD : ∀ y ∈ D, Tendsto (fun n => S n y) atTop (𝓝 (T y))) :
    ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (T x)) := by
  apply strong_tendsto_of_dense_set S T B hB hbound _ hdense
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hD y hy
  | zero => simpa only [map_zero] using tendsto_const_nhds
  | add x y hx hy hx' hy' => simpa only [map_add] using hx'.add hy'
  | smul a x hx hx' => simpa only [map_smul] using hx'.const_smul a

end SurveyStatements.P4
