import ThesisCommon.Analysis.SequenceBlockTailBounds

/-! Column bounds determine the operator norm on actual ell1 spaces.
The diagonal-error estimate splits each column into its finite earlier
coordinates and its entire future tail. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem ellOne_opNorm_le_of_columns {ι : Type*} [DecidableEq ι] (T : EllOneSum ι X →L[𝕜] Y)
    {C : ℝ} (hC : 0 ≤ C)
    (hcol : ∀ i, ‖T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => X) 1 i)‖ ≤ C) :
    ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound T hC
  intro x
  have hs := (lp.hasSum_single (p := 1) (by simp) x).map T.toAddMonoidHom T.continuous
  have hn : HasSum (fun i => ‖x i‖) ‖x‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using lp.hasSum_norm (p := 1) (by simp) x
  apply hs.norm_le_of_bounded (hn.mul_left C)
  intro i
  exact ((T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => X) 1 i)).le_opNorm (x i)).trans
    (mul_le_mul_of_nonneg_right (hcol i) (norm_nonneg _))

theorem lpDiagonalPart_single {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) (j : ℕ) (x : X) :
    lpDiagonalPart T (lp.single p j x) = lp.single p j (lpEntry T j j x) := by
  ext k
  by_cases hk : k = j
  · subst k; simp
  · simp [hk]

theorem ellOne_sub_diagonal_column_prefix_tail
    (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) (j : ℕ) (x : X) :
    (T - lpDiagonalPart T) (lp.single 1 j x) =
      (∑ i ∈ Finset.range j, lp.single (E := fun _ : ℕ => X) 1 i (lpEntry T i j x)) +
      lpExtend (𝕜 := 𝕜) 1 (coordinateTail (Function.Embedding.refl ℕ) j)
        (lpRestrict (𝕜 := 𝕜) 1 (coordinateTail (Function.Embedding.refl ℕ) j)
          (T (lp.single 1 j x))) := by
  have h := lpPrefix_add_tail (𝕜 := 𝕜) j (T (lp.single 1 j x))
  rw [lpPrefix_eq_sum_single, Finset.sum_range_succ] at h
  rw [ContinuousLinearMap.sub_apply, lpDiagonalPart_single]
  conv_lhs => arg 1; rw [← h]
  simp only [lpEntry_apply]
  abel

theorem ellOne_norm_sub_diagonal_le_of_tail
    (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hearlier : ∀ j, (∑ i ∈ Finset.range j, ‖lpEntry T i j‖) ≤ a)
    (htail : ∀ j, ‖((lpRestrict 1 (coordinateTail (Function.Embedding.refl ℕ) j)).comp T).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 j)‖ ≤ b) :
    ‖T - lpDiagonalPart T‖ ≤ a+b := by
  apply ellOne_opNorm_le_of_columns _ (add_nonneg ha hb)
  intro j
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg ha hb)
  intro x
  change ‖(T - lpDiagonalPart T) (lp.single 1 j x)‖ ≤ (a+b) * ‖x‖
  rw [ellOne_sub_diagonal_column_prefix_tail]
  let s := coordinateTail (Function.Embedding.refl ℕ) j
  have hfinite : ‖∑ i ∈ Finset.range j, lp.single (E := fun _ : ℕ => X) 1 i (lpEntry T i j x)‖ ≤ a * ‖x‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range j, ‖lp.single (E := fun _ : ℕ => X) 1 i (lpEntry T i j x)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range j, ‖lpEntry T i j x‖ := by simp only [lp.norm_single (by simp : (0 : ℝ≥0∞) < 1)]
      _ ≤ ∑ i ∈ Finset.range j, ‖lpEntry T i j‖ * ‖x‖ :=
        Finset.sum_le_sum (fun i _ => (lpEntry T i j).le_opNorm x)
      _ = (∑ i ∈ Finset.range j, ‖lpEntry T i j‖) * ‖x‖ := (Finset.sum_mul ..).symm
      _ ≤ a * ‖x‖ := mul_le_mul_of_nonneg_right (hearlier j) (norm_nonneg x)
  have hfuture : ‖lpExtend (𝕜 := 𝕜) 1 s (lpRestrict (𝕜 := 𝕜) 1 s (T (lp.single 1 j x)))‖ ≤ b * ‖x‖ := by
    apply le_trans ((lpExtend (𝕜 := 𝕜) (X := X) 1 s).le_opNorm _) _
    apply le_trans (mul_le_mul_of_nonneg_right (norm_lpExtend_le s) (norm_nonneg _)) _
    rw [one_mul]
    exact ((((lpRestrict 1 s).comp T).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 j)).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (htail j) (norm_nonneg x))
  calc
    _ ≤ ‖∑ i ∈ Finset.range j, lp.single (E := fun _ : ℕ => X) 1 i (lpEntry T i j x)‖ +
      ‖lpExtend (𝕜 := 𝕜) 1 s (lpRestrict (𝕜 := 𝕜) 1 s (T (lp.single 1 j x)))‖ := norm_add_le _ _
    _ ≤ a * ‖x‖ + b * ‖x‖ := add_le_add hfinite hfuture
    _ = (a+b) * ‖x‖ := (add_mul ..).symm

end ThesisCommon


