import BanachIsometric.LocalIsometricFrames

/-! The actual orthogonal-hyperplane projection has a global operator
Lipschitz bound on the genuine Euclidean unit sphere. -/

namespace BanachIsometric

open Set
open scoped NNReal

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def normalHyperplane (u : Metric.sphere (0 : F) 1) : Submodule ℝ F := (ℝ ∙ u.val)ᗮ

omit [FiniteDimensional ℝ F] in
set_option maxHeartbeats 800000 in
theorem lipschitzWith_unit_span_projection :
    LipschitzWith 2 (fun u : Metric.sphere (0 : F) 1 => (ℝ ∙ u.val).starProjection) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hu : ‖u.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hv : ‖v.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  norm_num only [NNReal.coe_ofNat]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [ContinuousLinearMap.sub_apply, Submodule.starProjection_unit_singleton ℝ hu,
    Submodule.starProjection_unit_singleton ℝ hv]
  have heq : inner ℝ u.val x • u.val - inner ℝ v.val x • v.val =
      inner ℝ u.val x • (u.val - v.val) + inner ℝ (u.val - v.val) x • v.val := by
    rw [inner_sub_left, smul_sub, sub_smul]
    abel
  calc
    _ = ‖inner ℝ u.val x • (u.val - v.val) + inner ℝ (u.val - v.val) x • v.val‖ := congrArg norm heq
    _ ≤ ‖inner ℝ u.val x • (u.val - v.val)‖ + ‖inner ℝ (u.val - v.val) x • v.val‖ := norm_add_le _ _
    _ = ‖inner ℝ u.val x‖ * ‖u.val - v.val‖ + ‖inner ℝ (u.val - v.val) x‖ * ‖v.val‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ (‖u.val‖ * ‖x‖) * ‖u.val - v.val‖ + (‖u.val - v.val‖ * ‖x‖) * ‖v.val‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _))
    _ = (2 * ‖u.val - v.val‖) * ‖x‖ := by rw [hu, hv]; ring

theorem lipschitzWith_normalHyperplane_projection :
    LipschitzWith 2 (fun u : Metric.sphere (0 : F) 1 => (normalHyperplane u).starProjection) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [normalHyperplane, normalHyperplane, Submodule.starProjection_orthogonal',
    Submodule.starProjection_orthogonal']
  calc
    _ = dist ((ℝ ∙ u.val).starProjection) ((ℝ ∙ v.val).starProjection) := by
      rw [dist_eq_norm, dist_eq_norm,
        show (1 - (ℝ ∙ u.val).starProjection) - (1 - (ℝ ∙ v.val).starProjection) =
          -((ℝ ∙ u.val).starProjection - (ℝ ∙ v.val).starProjection) by abel,
        norm_neg]
    _ ≤ (2 : ℝ) * dist u v := lipschitzWith_unit_span_projection.dist_le_mul u v

theorem lipschitzWith_normalHyperplane_family {P : Type*} [PseudoMetricSpace P]
    (normal : P → Metric.sphere (0 : F) 1) {L : ℝ≥0} (hL : LipschitzWith L normal) :
    LipschitzWith (2 * L) (fun a => (normalHyperplane (normal a)).starProjection) :=
  lipschitzWith_normalHyperplane_projection.comp hL

end
end BanachIsometric
