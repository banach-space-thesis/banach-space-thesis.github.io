import JLMS.Definitions
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Small vectors with large images under a discontinuous linear map

This elementary rescaling lemma will supply the diagonal sequence in Johnson's
automatic-continuity argument. The witness has an arbitrarily small prescribed
norm and an arbitrarily large prescribed image norm.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_small_large_of_not_continuous (f : E →ₗ[𝕜] F) (hf : ¬ Continuous f)
    {ε : ℝ} (hε : 0 < ε) (M : ℝ) : ∃ x, ‖x‖ ≤ ε ∧ M < ‖f x‖ := by
  have hunbounded (C : ℝ) : ∃ x, C * ‖x‖ < ‖f x‖ := by
    by_contra h
    push_neg at h
    exact hf (AddMonoidHomClass.continuous_of_bound f C h)
  obtain ⟨x, hx⟩ := hunbounded ((|M| + 1) / ε)
  have hxne : x ≠ 0 := by intro h; simp [h] at hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  let c : ℝ := ε / ‖x‖
  have hc : 0 < c := div_pos hε hxpos
  refine ⟨(c : 𝕜) • x, ?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hc]
    exact (div_mul_cancel₀ ε hxpos.ne').le
  · rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos hc]
    have hh := mul_lt_mul_of_pos_left hx hc
    have heq : c * (((|M| + 1) / ε) * ‖x‖) = |M| + 1 := by
      dsimp [c]
      field_simp
    rw [heq] at hh
    exact (lt_of_le_of_lt (le_abs_self M) (by linarith : |M| < |M| + 1)).trans hh

end JLMS
