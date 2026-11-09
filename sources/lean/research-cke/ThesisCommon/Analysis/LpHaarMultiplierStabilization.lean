import ThesisCommon.Analysis.LpHaarBlockCompression
import ThesisCommon.Analysis.LpHaarInfiniteTraceSelection

/-! Actual contractive scalar compression of every bounded Haar multiplier,
with arbitrarily small error on the genuine mean-zero interval Lp space.
The estimate follows from a summable tree-edge variation budget. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem lpHaar_multiplier_scalar_compression
    (D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (d : ∀ n, Fin (2 ^ n) → 𝕜)
    (hD : ∀ n (k : Fin (2 ^ n)), D (lpHaarDyadic 𝕜 p n k) = d n k • lpHaarDyadic 𝕜 p n k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p, ∃ c : 𝕜,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ A.comp B = ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) ∧
      (∀ f, lpHaarIntegral (A f) = lpHaarIntegral f) ∧
      (∀ f, lpHaarIntegral (B f) = lpHaarIntegral f) ∧
      ∀ f, lpHaarIntegral f = 0 →
        ‖((A.comp D).comp B) f - c • f‖ ≤ (ε / 2) * ‖f‖ := by
  let δ := ε / 24
  have hδ : 0 < δ := div_pos hε (by norm_num)
  have hd : ∀ n k, ‖d n k‖ ≤ 6 * ‖D‖ := by
    intro n k
    have h := lpHaar_operator_diagonal_norm_le 𝕜 p hp D n k
    rw [hD, map_smul, lpHaarDyadicCoefficient_apply_level, if_pos rfl, smul_eq_mul, mul_one] at h
    exact h
  obtain ⟨a, F, heq, hlevels, hg, hchild⟩ := lpHaar_infinite_trace_selection d
    (mul_nonneg (by norm_num) (norm_nonneg D)) hd (lpHaarTraceErrorBudget δ)
    (fun j => mul_pos hδ (pow_pos (by norm_num) _))
  let g (j : ℕ) := lpHaarSplitDiagonal d (F.node j)
  let t (j : ℕ) := lpHaarParentTrace a (F.node j).parent
  have hgt (j : ℕ) : ‖g j - t j‖ ≤ lpHaarTraceErrorBudget δ j := (hg j).le
  have htt (j : ℕ) (hj : j ≠ 0) : ‖t j - t ((j - 1) / 2)‖ ≤
      lpHaarTraceErrorBudget δ ((j - 1) / 2) := by
    have hparent := F.parent j
    simp only [lpHaarHistoryParent, dif_neg hj] at hparent
    dsimp only [t]
    rw [lpHaarParentTrace_congr a heq _ _ hparent]
    exact (hchild ((j - 1) / 2) (decide (j % 2 = 1))).le
  obtain ⟨hs, hsum⟩ := lpHaar_geometric_edge_budget g t hδ.le hgt htt
  obtain ⟨A, B, hA, hB, hAB, _, hAlim, hBlim⟩ :=
    F.toPartitionTree.exists_faithful_retraction 𝕜 p hp F.faithful
  refine ⟨A, B, t 0, hA, hB, hAB,
    F.toPartitionTree.reading_integral 𝕜 p hp A hAlim,
    F.toPartitionTree.embedding_integral 𝕜 p hp B hBlim, ?_⟩
  intro f hf
  have hdiag (n : ℕ) (k : Fin (2 ^ n)) :
      ((A.comp D).comp B) (lpHaarDyadic 𝕜 p n k) =
        g (lpHaarHeapIndex n k) • lpHaarDyadic 𝕜 p n k :=
    F.compression_multiplier 𝕜 p hp hlevels A B D hAlim hBlim d hD n k
  have h := lpHaar_diagonal_edge_meanZero_bound 𝕜 p hp ((A.comp D).comp B)
    (fun i => g (lpHaarHeapIndex i.1 i.2)) (t 0) hdiag hs f hf
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  have hscale : 12 * δ = ε / 2 := by dsimp only [δ]; ring
  nlinarith

end ThesisCommon
