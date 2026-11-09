import ThesisCommon.Analysis.LpDisjointSigns
import ThesisCommon.Analysis.EllOneSignedReduction
import ThesisCommon.Analysis.EllOneThreshold

/-! UPFP Lemmas 3.2 and 4.4: forward and backward reductions for ell1
outer sums, with finite-p, infinity and c0 inner spaces. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem lp_to_ellOne_forward_reduction (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (T : lp (fun _ : ℕ => X) p →L[𝕜] EllOneSum ℕ Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a m : ℕ ↪ ℕ), ‖((lpRestrict 1 m).comp T).comp (lpExtend p a)‖ < ε := by
  obtain ⟨n, hn⟩ := exists_ellOne_power_threshold (M := ‖T‖) hp hε
  obtain ⟨i, hi⟩ := exists_small_block_of_additive_target
    (fun i : Fin n => lpRestrict (𝕜 := 𝕜) (X := Y) 1 (disjointCoordinateEmbedding i))
    (ellOne_disjoint_restriction_sum_le n)
    (fun i : Fin n => lpExtend (𝕜 := 𝕜) (X := X) p (disjointCoordinateEmbedding i))
    (fun x hx θ => lp_disjoint_blocks_sign_bound p (zero_lt_one.trans hp) x hx θ)
    T hε (norm_nonneg T) le_rfl (ellOne_power_threshold hp (norm_nonneg T) hn)
  exact ⟨disjointCoordinateEmbedding i, disjointCoordinateEmbedding i, hi⟩

theorem infinity_to_ellOne_forward_reduction
    (T : EllInfinitySum X →L[𝕜] EllOneSum ℕ Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a m : ℕ ↪ ℕ), ‖((lpRestrict 1 m).comp T).comp (lpExtend ∞ a)‖ < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (‖T‖ / (ε / 2))
  have hlarge : ‖T‖ * 1 < (n : ℝ) * (ε/2) := by
    simpa only [mul_one] using (div_lt_iff₀ (half_pos hε)).mp hn
  obtain ⟨i, hi⟩ := exists_small_block_of_additive_target
    (fun i : Fin n => lpRestrict (𝕜 := 𝕜) (X := Y) 1 (disjointCoordinateEmbedding i))
    (ellOne_disjoint_restriction_sum_le n)
    (fun i : Fin n => lpExtend (𝕜 := 𝕜) (X := X) ∞ (disjointCoordinateEmbedding i))
    (fun x hx θ => infinity_disjoint_blocks_sign_bound x hx θ)
    T hε (norm_nonneg T) le_rfl hlarge
  exact ⟨disjointCoordinateEmbedding i, disjointCoordinateEmbedding i, hi⟩

theorem cZero_to_ellOne_forward_reduction
    (T : CZeroSum X →L[𝕜] EllOneSum ℕ Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a m : ℕ ↪ ℕ), ‖((lpRestrict 1 m).comp T).comp (cZeroExtend a)‖ < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (‖T‖ / (ε / 2))
  have hlarge : ‖T‖ * 1 < (n : ℝ) * (ε/2) := by
    simpa only [mul_one] using (div_lt_iff₀ (half_pos hε)).mp hn
  obtain ⟨i, hi⟩ := exists_small_block_of_additive_target
    (fun i : Fin n => lpRestrict (𝕜 := 𝕜) (X := Y) 1 (disjointCoordinateEmbedding i))
    (ellOne_disjoint_restriction_sum_le n)
    (fun i : Fin n => cZeroExtend (𝕜 := 𝕜) (X := X) (disjointCoordinateEmbedding i))
    (fun x hx θ => cZero_disjoint_blocks_sign_bound x hx θ)
    T hε (norm_nonneg T) le_rfl hlarge
  exact ⟨disjointCoordinateEmbedding i, disjointCoordinateEmbedding i, hi⟩

theorem lp_to_ellOne_backward_reduction (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    {n : ℕ} (T : lp (fun _ : ℕ => X) p →L[𝕜] EllOneSum (Fin n) Y) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 2 * ‖T‖ < (n : ℝ) ^ ((p.toReal-1)/p.toReal) * ε) :
    ∃ (i : Fin n) (a : ℕ ↪ ℕ), ‖((lpCoordinate 1 i).comp T).comp (lpExtend p a)‖ < ε := by
  obtain ⟨i, hi⟩ := exists_small_block_of_additive_target
    (fun i : Fin n => lpCoordinate (𝕜 := 𝕜) (X := Y) 1 i)
    (ellOne_finite_coordinate_sum_le n)
    (fun i : Fin n => lpExtend (𝕜 := 𝕜) (X := X) p (disjointCoordinateEmbedding i))
    (fun x hx θ => lp_disjoint_blocks_sign_bound p (zero_lt_one.trans hp) x hx θ)
    T hε (norm_nonneg T) le_rfl (ellOne_power_threshold hp (norm_nonneg T) hlarge)
  exact ⟨i, disjointCoordinateEmbedding i, hi⟩

theorem infinity_to_ellOne_backward_reduction {n : ℕ}
    (T : EllInfinitySum X →L[𝕜] EllOneSum (Fin n) Y) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 2 * ‖T‖ < (n : ℝ) * ε) :
    ∃ (i : Fin n) (a : ℕ ↪ ℕ), ‖((lpCoordinate 1 i).comp T).comp (lpExtend ∞ a)‖ < ε := by
  obtain ⟨i, hi⟩ := exists_small_block_of_additive_target
    (fun i : Fin n => lpCoordinate (𝕜 := 𝕜) (X := Y) 1 i)
    (ellOne_finite_coordinate_sum_le n)
    (fun i : Fin n => lpExtend (𝕜 := 𝕜) (X := X) ∞ (disjointCoordinateEmbedding i))
    (fun x hx θ => infinity_disjoint_blocks_sign_bound x hx θ)
    T hε (norm_nonneg T) le_rfl (show ‖T‖ * 1 < (n : ℝ) * (ε/2) by linarith)
  exact ⟨i, disjointCoordinateEmbedding i, hi⟩

theorem cZero_to_ellOne_backward_reduction {n : ℕ}
    (T : CZeroSum X →L[𝕜] EllOneSum (Fin n) Y) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 2 * ‖T‖ < (n : ℝ) * ε) :
    ∃ (i : Fin n) (a : ℕ ↪ ℕ), ‖((lpCoordinate 1 i).comp T).comp (cZeroExtend a)‖ < ε := by
  obtain ⟨i, hi⟩ := exists_small_block_of_additive_target
    (fun i : Fin n => lpCoordinate (𝕜 := 𝕜) (X := Y) 1 i)
    (ellOne_finite_coordinate_sum_le n)
    (fun i : Fin n => cZeroExtend (𝕜 := 𝕜) (X := X) (disjointCoordinateEmbedding i))
    (fun x hx θ => cZero_disjoint_blocks_sign_bound x hx θ)
    T hε (norm_nonneg T) le_rfl (show ‖T‖ * 1 < (n : ℝ) * (ε/2) by linarith)
  exact ⟨i, disjointCoordinateEmbedding i, hi⟩

end ThesisCommon
