import BanachIsometric.BoundaryHomotopyStability
import BanachIsometric.RegularBranches

/-!
# Actual derivative linearization isolates the complete affine homotopy

At a point with an invertible derivative, differentiability bounds the
remainder by half the linear part. The homotopy from the actual function
to its affine linearization consequently avoids the root value throughout
a punctured neighborhood. No local injectivity or inverse function theorem
is inferred from ordinary differentiability.
-/

namespace BanachIsometric

open Set Metric Filter
open scoped Topology

theorem exists_affine_linearization_avoids_root
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x : E} (L : E ≃L[ℝ] E)
    (hf : HasFDerivAt f (L : E →L[ℝ] E) x) :
    ∃ r > 0, ∀ z, dist z x < r → z ≠ x → ∀ t : unitInterval,
      realAffine t (f z) (f x + L (z - x)) ≠ f x := by
  let K : ℝ := ‖(L.symm : E →L[ℝ] E)‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let ε : ℝ := (2 * K)⁻¹
  have hε : 0 < ε := inv_pos.mpr (mul_pos (by norm_num) hK)
  have hεK : ε * K = 1 / 2 := by dsimp [ε]; field_simp
  have herr : ∀ᶠ z in 𝓝 x, ‖f z - f x - L (z - x)‖ ≤ ε * ‖z - x‖ :=
    Asymptotics.isLittleO_iff.mp hf.isLittleO hε
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp herr
  refine ⟨r, hr, fun z hz hzx t hzero => ?_⟩
  have hlin : ‖z - x‖ ≤ K * ‖L (z - x)‖ := by
    have h := (L.symm : E →L[ℝ] E).le_opNorm (L (z - x))
    change ‖L.symm (L (z - x))‖ ≤ ‖(L.symm : E →L[ℝ] E)‖ * ‖L (z - x)‖ at h
    rw [L.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _))
  have hrem : ‖f z - f x - L (z - x)‖ ≤ (1 / 2 : ℝ) * ‖L (z - x)‖ := by
    calc
      ‖f z - f x - L (z - x)‖ ≤ ε * ‖z - x‖ := hball (mem_ball.mpr hz)
      _ ≤ ε * (K * ‖L (z - x)‖) := mul_le_mul_of_nonneg_left hlin hε.le
      _ = (1 / 2 : ℝ) * ‖L (z - x)‖ := by rw [← mul_assoc, hεK]
  have hdist := dist_realAffine_le_add t (f z) (f x + L (z - x))
    (f x + L (z - x)) (f x + L (z - x))
  rw [realAffine_self, dist_self, add_zero, hzero] at hdist
  have hleft : dist (f x) (f x + L (z - x)) = ‖L (z - x)‖ := by
    rw [dist_eq_norm, show f x - (f x + L (z - x)) = -L (z - x) by abel, norm_neg]
  have hright : dist (f z) (f x + L (z - x)) = ‖f z - f x - L (z - x)‖ := by
    rw [dist_eq_norm, sub_add_eq_sub_sub]
  rw [hleft, hright] at hdist
  have hpos : 0 < ‖L (z - x)‖ := by
    apply norm_pos_iff.mpr
    intro heq
    exact (sub_ne_zero.mpr hzx) (L.injective (heq.trans L.map_zero.symm))
  linarith

end BanachIsometric
