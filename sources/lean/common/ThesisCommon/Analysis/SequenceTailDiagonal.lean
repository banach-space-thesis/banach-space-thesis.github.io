import ThesisCommon.Analysis.SequenceOffDiagonal
import ThesisCommon.Analysis.SequenceEntryAlgebra

/-! A direct diagonal-error criterion using finite earlier entries and the
whole future-tail action. This is the final estimate in UPFP Proposition 5.4.
It applies to arbitrary infinity operators without matrix determination.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem infinity_sub_diagonal_prefix_tail
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) (x : EllInfinitySum X) (k : ℕ) :
    (T - lpDiagonalPart T) x k = (∑ j ∈ Finset.range k, lpEntry T k j (x j)) +
      T (lpExtend (𝕜 := 𝕜) ∞ (coordinateTail (Function.Embedding.refl ℕ) k)
        (lpRestrict (𝕜 := 𝕜) ∞ (coordinateTail (Function.Embedding.refl ℕ) k) x)) k := by
  have h := congrArg (fun z : EllInfinitySum X => T z k) (lpPrefix_add_tail (𝕜 := 𝕜) k x)
  simp only [map_add, lp.coeFn_add, Pi.add_apply] at h
  have hp : T (lpPrefix k x) k = ∑ j ∈ Finset.range (k+1), T (lp.single ∞ j (x j)) k := by
    rw [lpPrefix_eq_sum_single, map_sum]
    change (lpCoordinate (𝕜 := 𝕜) ∞ k) (∑ j ∈ Finset.range (k+1), T (lp.single ∞ j (x j))) = _
    rw [map_sum]
    rfl
  rw [hp, Finset.sum_range_succ] at h
  change T x k - T (lp.single ∞ k (x k)) k = _
  rw [← h]
  simp only [lpEntry_apply]
  abel

theorem cZero_sub_diagonal_prefix_tail
    (T : CZeroSum X →L[𝕜] CZeroSum X) (x : CZeroSum X) (k : ℕ) :
    (T - cZeroDiagonalPart T) x k = (∑ j ∈ Finset.range k, cZeroEntry T k j (x j)) +
      T (cZeroExtend (𝕜 := 𝕜) (coordinateTail (Function.Embedding.refl ℕ) k)
        (cZeroRestrict (𝕜 := 𝕜) (coordinateTail (Function.Embedding.refl ℕ) k) x)) k := by
  have h := congrArg (fun z : CZeroSum X => T z k) (cZeroPrefix_add_tail (𝕜 := 𝕜) k x)
  simp only [map_add, ZeroAtInftyContinuousMap.add_apply] at h
  have hp : T (cZeroPrefix k x) k =
      ∑ j ∈ Finset.range (k+1), T (cZeroSingle j (x j)) k := by
    rw [cZeroPrefix_eq_sum_single, map_sum]
    change (cZeroCoordinate (𝕜 := 𝕜) k) (∑ j ∈ Finset.range (k+1), T (cZeroSingle j (x j))) = _
    rw [map_sum]
    rfl
  rw [hp, Finset.sum_range_succ] at h
  change T x k - T (cZeroSingle k (x k)) k = _
  rw [← h]
  simp only [cZeroEntry_apply]
  abel

private theorem norm_finite_row_le (F : ℕ → X →L[𝕜] X) (x : ℕ → X) (k : ℕ)
    {a B : ℝ} (hB : 0 ≤ B) (hx : ∀ i, ‖x i‖ ≤ B)
    (hsum : (∑ i ∈ Finset.range k, ‖F i‖) ≤ a) :
    ‖∑ i ∈ Finset.range k, F i (x i)‖ ≤ a * B := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, ‖F i (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range k, ‖F i‖ * B := Finset.sum_le_sum (fun i _ =>
      ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)))
    _ = (∑ i ∈ Finset.range k, ‖F i‖) * B := (Finset.sum_mul ..).symm
    _ ≤ a * B := mul_le_mul_of_nonneg_right hsum hB

/-- Earlier finite entries and the entire future tail bound the diagonal error. -/
theorem infinity_norm_sub_diagonal_le_of_tail
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hearlier : ∀ k, (∑ j ∈ Finset.range k, ‖lpEntry T k j‖) ≤ a)
    (htail : ∀ k, ‖((lpCoordinate ∞ k).comp T).comp
      (lpExtend (𝕜 := 𝕜) ∞ (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ b) :
    ‖T - lpDiagonalPart T‖ ≤ a + b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg ha hb)
  intro x
  apply lp.norm_le_of_forall_le (mul_nonneg (add_nonneg ha hb) (norm_nonneg x))
  intro k
  rw [infinity_sub_diagonal_prefix_tail]
  let s := coordinateTail (Function.Embedding.refl ℕ) k
  have hrestrict : ‖lpRestrict (𝕜 := 𝕜) ∞ s x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖lpRestrict (𝕜 := 𝕜) (X := X) ∞ s‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (norm_lpRestrict_le s) (norm_nonneg x)
      _ = _ := one_mul _
  have hfuture : ‖T (lpExtend (𝕜 := 𝕜) ∞ s (lpRestrict (𝕜 := 𝕜) ∞ s x)) k‖ ≤ b * ‖x‖ := by
    exact ((((lpCoordinate ∞ k).comp T).comp (lpExtend (𝕜 := 𝕜) ∞ s)).le_opNorm _).trans
      (mul_le_mul (htail k) hrestrict (norm_nonneg _) hb)
  calc
    _ ≤ ‖∑ j ∈ Finset.range k, lpEntry T k j (x j)‖ +
        ‖T (lpExtend (𝕜 := 𝕜) ∞ s (lpRestrict (𝕜 := 𝕜) ∞ s x)) k‖ := norm_add_le _ _
    _ ≤ a * ‖x‖ + b * ‖x‖ := add_le_add
      (norm_finite_row_le (lpEntry T k) x k (norm_nonneg x)
        (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero x i) (hearlier k)) hfuture
    _ = (a + b) * ‖x‖ := (add_mul ..).symm

/-- The same direct estimate on actual null sequences. -/
theorem cZero_norm_sub_diagonal_le_of_tail
    (T : CZeroSum X →L[𝕜] CZeroSum X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hearlier : ∀ k, (∑ j ∈ Finset.range k, ‖cZeroEntry T k j‖) ≤ a)
    (htail : ∀ k, ‖((cZeroCoordinate k).comp T).comp
      (cZeroExtend (𝕜 := 𝕜) (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ b) :
    ‖T - cZeroDiagonalPart T‖ ≤ a + b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg ha hb)
  intro x
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (add_nonneg ha hb) (norm_nonneg x))).mpr
  intro k
  change ‖(T - cZeroDiagonalPart T) x k‖ ≤ (a+b) * ‖x‖
  rw [cZero_sub_diagonal_prefix_tail]
  let s := coordinateTail (Function.Embedding.refl ℕ) k
  have hrestrict : ‖cZeroRestrict (𝕜 := 𝕜) s x‖ ≤ ‖x‖ := norm_cZeroRead_le s x
  have hfuture : ‖T (cZeroExtend (𝕜 := 𝕜) s (cZeroRestrict (𝕜 := 𝕜) s x)) k‖ ≤ b * ‖x‖ := by
    exact ((((cZeroCoordinate k).comp T).comp (cZeroExtend (𝕜 := 𝕜) s)).le_opNorm _).trans
      (mul_le_mul (htail k) hrestrict (norm_nonneg (cZeroRestrict (𝕜 := 𝕜) s x)) hb)
  calc
    _ ≤ ‖∑ j ∈ Finset.range k, cZeroEntry T k j (x j)‖ +
        ‖T (cZeroExtend (𝕜 := 𝕜) s (cZeroRestrict (𝕜 := 𝕜) s x)) k‖ := norm_add_le _ _
    _ ≤ a * ‖x‖ + b * ‖x‖ := add_le_add
      (norm_finite_row_le (cZeroEntry T k) x k (norm_nonneg x)
        (fun i => BoundedContinuousFunction.norm_coe_le_norm x.toBCF i) (hearlier k)) hfuture
    _ = (a + b) * ‖x‖ := (add_mul ..).symm

end ThesisCommon

