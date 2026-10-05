import ThesisCommon.Analysis.CotypeOperators
import ThesisCommon.Analysis.DisjointSequenceBlocks
import ThesisCommon.Analysis.SequenceCoordinates

/-! Finite-cotype forward reduction for c₀ and ℓ∞, UPFP Lemma 3.4.
The finite domain is mathlib's actual ℓ∞ over Fin n, with its sup norm.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Cotype selects a column whose entries are small on infinitely many rows
of an operator from a finite ℓ∞ sum to an infinite ℓ∞ sum. -/
theorem HasRademacherCotype.infinity_forward_reduction {q C : ℝ}
    (h : HasRademacherCotype X q C) {n : ℕ}
    (T : lp (fun _ : Fin n => Y) ∞ →L[𝕜] EllInfinitySum X) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 2 * C * ‖T‖ < (n : ℝ) ^ (1 / q) * ε) :
    ∃ i : Fin n, {m : ℕ | ‖((lpCoordinate ∞ m).comp T).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)‖ < ε}.Infinite := by
  refine h.infinite_small_block
    (fun i => lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)
    (fun x hx θ => infinity_single_blocks_sign_bound (𝕜 := 𝕜) x hx θ)
    (fun m => (lpCoordinate ∞ m).comp T) hε (norm_nonneg T) ?_ hlarge
  intro m
  calc
    _ ≤ ‖lpCoordinate (𝕜 := 𝕜) (X := X) ∞ m‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_lpCoordinate_le ∞ m) (norm_nonneg T)
    _ = ‖T‖ := one_mul _

/-- The same forward selection holds with target c₀, using its bounded
coordinate evaluations and the identical finite-domain test vectors. -/
theorem HasRademacherCotype.cZero_forward_reduction {q C : ℝ}
    (h : HasRademacherCotype X q C) {n : ℕ}
    (T : lp (fun _ : Fin n => Y) ∞ →L[𝕜] CZeroSum X) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 2 * C * ‖T‖ < (n : ℝ) ^ (1 / q) * ε) :
    ∃ i : Fin n, {m : ℕ | ‖((cZeroCoordinate m).comp T).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)‖ < ε}.Infinite := by
  refine h.infinite_small_block
    (fun i => lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)
    (fun x hx θ => infinity_single_blocks_sign_bound (𝕜 := 𝕜) x hx θ)
    (fun m => (cZeroCoordinate m).comp T) hε (norm_nonneg T) ?_ hlarge
  intro m
  calc
    _ ≤ ‖cZeroCoordinate (𝕜 := 𝕜) (X := X) m‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_cZeroCoordinate_le m) (norm_nonneg T)
    _ = ‖T‖ := one_mul _

end ThesisCommon
