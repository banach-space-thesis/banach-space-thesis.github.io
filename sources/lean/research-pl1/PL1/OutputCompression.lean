import PL1.MatrixTrace

/-! # Output truncation from summable operator columns

For a fixed finite set of input coordinates, summability of each column's
operator norms gives convergence of output truncations in operator norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Filter
open scoped Topology ENNReal BigOperators

namespace PL1.OutputCompression

open MatrixTrace

variable {𝕜 Y : Type*} [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The norm omitted by a coordinate truncation is exactly its scalar tail sum. -/
theorem norm_sub_compression_range (N : ℕ) (x : L1Sum Y) :
    ‖x - compression (𝕜 := 𝕜) (Finset.range N) x‖ = ∑' i : ℕ, ‖x (i + N)‖ := by
  rw [compression_apply]
  have h := lp.norm_compl_sum_single (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
    x (Finset.range N)
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  have ht := (L1Sum.summable_norm x).sum_add_tsum_nat_add N
  rw [← L1Sum.norm_eq_tsum] at ht
  linarith

/-- An output tail of a single operator column is bounded by its column norm tail. -/
theorem norm_tail_column_le (Q : L1Sum Y →L[𝕜] L1Sum Y) (j : ℕ)
    (hcol : Summable (fun i => ‖entry Q i j‖)) (N : ℕ) :
    ‖(ContinuousLinearMap.id 𝕜 (L1Sum Y) - compression (Finset.range N)).comp
      (Q.comp (insertion j))‖ ≤ ∑' i : ℕ, ‖entry Q (i + N) j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg (fun _ => norm_nonneg _))
  intro y
  change ‖Q (insertion j y) - compression (Finset.range N) (Q (insertion j y))‖ ≤ _
  rw [norm_sub_compression_range (𝕜 := 𝕜) N (Q (insertion j y))]
  change (∑' i : ℕ, ‖entry Q (i + N) j y‖) ≤ _
  have hy0 : Summable (fun i : ℕ => ‖entry Q i j y‖) := by
    change Summable (fun i : ℕ => ‖Q (insertion j y) i‖)
    exact L1Sum.summable_norm (Q (insertion j y))
  have hy : Summable (fun i : ℕ => ‖entry Q (i + N) j y‖) :=
    (summable_nat_add_iff N).mpr hy0
  have hs : Summable (fun i : ℕ => ‖entry Q (i + N) j‖) :=
    (summable_nat_add_iff N).mpr hcol
  calc
    _ ≤ ∑' i : ℕ, ‖entry Q (i + N) j‖ * ‖y‖ :=
      Summable.tsum_le_tsum (fun i => (entry Q (i + N) j).le_opNorm y) hy (hs.mul_right ‖y‖)
    _ = _ := tsum_mul_right

/-- Summability is used to bound the actual column, before taking scalar series tails. -/
theorem norm_tail_column_tendsto_zero (Q : L1Sum Y →L[𝕜] L1Sum Y) (j : ℕ)
    (hcol : Summable (fun i => ‖entry Q i j‖)) :
    Tendsto (fun N => ‖(ContinuousLinearMap.id 𝕜 (L1Sum Y) - compression (Finset.range N)).comp
      (Q.comp (insertion j))‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (norm_tail_column_le Q j hcol)
    (tendsto_sum_nat_add (fun i => ‖entry Q i j‖))

/-- Output truncations converge in operator norm after any fixed finite input compression. -/
theorem tendsto_output_compression (Q : L1Sum Y →L[𝕜] L1Sum Y)
    (hcolumns : ∀ j, Summable (fun i => ‖entry Q i j‖)) (F : Finset ℕ) :
    Tendsto (fun N => ‖(ContinuousLinearMap.id 𝕜 (L1Sum Y) - compression (Finset.range N)).comp
      (Q.comp (compression F))‖) atTop (𝓝 0) := by
  let C (N j : ℕ) : Y →L[𝕜] L1Sum Y :=
    (ContinuousLinearMap.id 𝕜 (L1Sum Y) - compression (Finset.range N)).comp
      (Q.comp (insertion j))
  have heq (N : ℕ) :
      (ContinuousLinearMap.id 𝕜 (L1Sum Y) - compression (Finset.range N)).comp
        (Q.comp (compression F)) = ∑ j ∈ F, (C N j).comp (coordinate j) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [C, compression, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, map_sum, sum_apply]
  have hbound (N : ℕ) :
      ‖(ContinuousLinearMap.id 𝕜 (L1Sum Y) - compression (Finset.range N)).comp
        (Q.comp (compression F))‖ ≤ ∑ j ∈ F, ‖C N j‖ * ‖coordinate (𝕜 := 𝕜) (Y := Y) j‖ := by
    rw [heq]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun j _ => ContinuousLinearMap.opNorm_comp_le _ _))
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  have h := tendsto_finsetSum F (fun j _ =>
    (norm_tail_column_tendsto_zero Q j (hcolumns j)).mul_const
      ‖coordinate (𝕜 := 𝕜) (Y := Y) j‖)
  simpa only [C, zero_mul, Finset.sum_const_zero] using h

end PL1.OutputCompression

