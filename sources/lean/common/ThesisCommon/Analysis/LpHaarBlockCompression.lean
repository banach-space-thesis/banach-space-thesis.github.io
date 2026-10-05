import ThesisCommon.Analysis.LpHaarSequentialGeometry
import ThesisCommon.Analysis.LpHaarRetractionMeanZero
import ThesisCommon.Analysis.LpHaarNormalizedTraces
import ThesisCommon.Analysis.LpHaarGeometricEdgeBudget

/-! Exact matrix entries of the actual infinite block compression.
Strictly separated underlying levels preserve diagonal operators. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

namespace LpHaarSequentialSplits
variable (F : LpHaarSequentialSplits)

theorem nodeReader_eq (n : ℕ) (k : Fin (2 ^ n)) :
    F.toPartitionTree.nodeReader 𝕜 p n k = (F.node (lpHaarHeapIndex n k)).reader 𝕜 p := by
  let S := F.node (lpHaarHeapIndex n k)
  apply F.toPartitionTree.nodeReader_signed 𝕜 p n k S.level S.atoms S.signs
  · change F.cell (n + 1) (lpHaarLeftIndex n k) = _
    rw [F.cell_left, LpHaarFiniteSplit.child_set]
    rfl
  · change F.cell (n + 1) (lpHaarRightIndex n k) = _
    rw [F.cell_right, LpHaarFiniteSplit.child_set]
    rfl

theorem nodeVector_eq (n : ℕ) (k : Fin (2 ^ n)) :
    F.toPartitionTree.nodeVector 𝕜 p n k = (F.node (lpHaarHeapIndex n k)).vector 𝕜 p := by
  let S := F.node (lpHaarHeapIndex n k)
  rw [LpHaarFiniteSplit.vector, lpHaarSignedBlock_eq_vector]
  have hl : F.cell (n + 1) (lpHaarLeftIndex n k) = lpHaarSignedPart S.level S.atoms S.signs := by
    rw [F.cell_left, LpHaarFiniteSplit.child_set]
    rfl
  have hr : F.cell (n + 1) (lpHaarRightIndex n k) =
      lpHaarSignedPart S.level S.atoms (fun j => !(S.signs j)) := by
    rw [F.cell_right, LpHaarFiniteSplit.child_set]
    rfl
  change lpHaarVector 𝕜 p.val (F.cell (n + 1) (lpHaarLeftIndex n k))
    (F.cell (n + 1) (lpHaarRightIndex n k)) _ _ = _
  have hcongr {s t s' t' : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hs' : MeasurableSet s') (ht' : MeasurableSet t') (he : s = s') (he' : t = t') :
      lpHaarVector (μ := volume.restrict (Icc (0 : ℝ) 1)) 𝕜 p.val s t hs ht =
        lpHaarVector 𝕜 p.val s' t' hs' ht' := by
    subst s'
    subst t'
    rfl
  exact hcongr _ _ _ _ hl hr

theorem compression_coefficient
    (A B T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hA : ∀ f, Tendsto (fun m => F.toPartitionTree.backward 𝕜 p hp m f) atTop (𝓝 (A f)))
    (hB : ∀ f, Tendsto (fun m => F.toPartitionTree.forward 𝕜 p hp m f) atTop (𝓝 (B f)))
    (n m : ℕ) (k : Fin (2 ^ n)) (l : Fin (2 ^ m)) :
    lpHaarDyadicCoefficient 𝕜 p n k (((A.comp T).comp B) (lpHaarDyadic 𝕜 p m l)) =
      (F.node (lpHaarHeapIndex n k)).reader 𝕜 p
        (T ((F.node (lpHaarHeapIndex m l)).vector 𝕜 p)) := by
  change lpHaarDyadicCoefficient 𝕜 p n k (A (T (B (lpHaarDyadic 𝕜 p m l)))) = _
  rw [F.toPartitionTree.reading_coefficient 𝕜 p hp A hA,
    F.toPartitionTree.embedding_haar 𝕜 p hp B hB, F.nodeReader_eq 𝕜 p, F.nodeVector_eq 𝕜 p]

theorem block_norm_eq (B : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hB : ∀ f, Tendsto (fun m => F.toPartitionTree.forward 𝕜 p hp m f) atTop (𝓝 (B f)))
    (hiso : ∀ f, ‖B f‖ = ‖f‖) (n : ℕ) (k : Fin (2 ^ n)) :
    ‖(F.node (lpHaarHeapIndex n k)).vector 𝕜 p‖ = ‖lpHaarDyadic 𝕜 p n k‖ := by
  rw [← F.nodeVector_eq 𝕜 p, ← F.toPartitionTree.embedding_haar 𝕜 p hp B hB, hiso]

end LpHaarSequentialSplits

include hp in
theorem lpHaarFiniteSplit_reader_multiplier_other (S R : LpHaarFiniteSplit)
    (hSR : R.level ≠ S.level) (D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (d : ∀ n, Fin (2 ^ n) → 𝕜)
    (hD : ∀ n (k : Fin (2 ^ n)), D (lpHaarDyadic 𝕜 p n k) = d n k • lpHaarDyadic 𝕜 p n k) :
    S.reader 𝕜 p (D (R.vector 𝕜 p)) = 0 := by
  rw [LpHaarFiniteSplit.reader, lpHaarSignedBlockReader_apply]
  have hz (k : Fin (2 ^ S.level)) : lpHaarDyadicCoefficient 𝕜 p S.level k (D (R.vector 𝕜 p)) = 0 := by
    rw [LpHaarFiniteSplit.vector, lpHaarSignedBlock, map_sum, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    cases R.signs j <;> simp only [signedValue, if_true, Bool.false_eq_true, if_false,
      map_neg, hD, map_smul, lpHaarDyadicCoefficient_other_level 𝕜 p hp R.level S.level j k hSR.symm,
      smul_zero, neg_zero]
  simp_rw [hz]
  have hsign (k : Fin (2 ^ S.level)) : signedValue (S.signs k) (0 : 𝕜) = 0 := by
    cases S.signs k <;> simp [signedValue]
  simp_rw [hsign]
  simp

theorem lpHaarFiniteSplit_integral_multiplier (S : LpHaarFiniteSplit)
    (D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (d : ∀ n, Fin (2 ^ n) → 𝕜)
    (hD : ∀ n (k : Fin (2 ^ n)), D (lpHaarDyadic 𝕜 p n k) = d n k • lpHaarDyadic 𝕜 p n k) :
    lpHaarIntegral (D (S.vector 𝕜 p)) = 0 := by
  rw [LpHaarFiniteSplit.vector, lpHaarSignedBlock, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  cases S.signs j <;> simp only [signedValue, if_true, Bool.false_eq_true, if_false,
    map_neg, hD, map_smul, lpHaarIntegral_apply,
    lpHaarDyadic_integral_zero 𝕜 p S.level j j.isLt, smul_zero, neg_zero]

namespace LpHaarSequentialSplits
variable (F : LpHaarSequentialSplits)

theorem compression_multiplier (hlevels : ∀ i j, i < j → (F.node i).level < (F.node j).level)
    (A B D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hA : ∀ f, Tendsto (fun m => F.toPartitionTree.backward 𝕜 p hp m f) atTop (𝓝 (A f)))
    (hB : ∀ f, Tendsto (fun m => F.toPartitionTree.forward 𝕜 p hp m f) atTop (𝓝 (B f)))
    (d : ∀ n, Fin (2 ^ n) → 𝕜)
    (hD : ∀ n (k : Fin (2 ^ n)), D (lpHaarDyadic 𝕜 p n k) = d n k • lpHaarDyadic 𝕜 p n k)
    (n : ℕ) (k : Fin (2 ^ n)) :
    ((A.comp D).comp B) (lpHaarDyadic 𝕜 p n k) =
      lpHaarSplitDiagonal d (F.node (lpHaarHeapIndex n k)) • lpHaarDyadic 𝕜 p n k := by
  let c := lpHaarSplitDiagonal d (F.node (lpHaarHeapIndex n k))
  have hc : ∀ i : Option LpHaarTreeIndex,
      lpHaarRawCoordinate 𝕜 p i (((A.comp D).comp B) (lpHaarDyadic 𝕜 p n k)) =
        lpHaarRawCoordinate 𝕜 p i (c • lpHaarDyadic 𝕜 p n k) := by
    intro i
    cases i with
    | none =>
        change lpHaarIntegral (A (D (B (lpHaarDyadic 𝕜 p n k)))) = lpHaarIntegral (c • lpHaarDyadic 𝕜 p n k)
        rw [F.toPartitionTree.reading_integral 𝕜 p hp A hA,
          F.toPartitionTree.embedding_haar 𝕜 p hp B hB, F.nodeVector_eq 𝕜 p,
          lpHaarFiniteSplit_integral_multiplier 𝕜 p _ D d hD,
          map_smul, lpHaarIntegral_apply, lpHaarDyadic_integral_zero 𝕜 p n k k.isLt, smul_zero]
    | some i =>
        rcases i with ⟨m, l⟩
        change lpHaarDyadicCoefficient 𝕜 p m l (((A.comp D).comp B) (lpHaarDyadic 𝕜 p n k)) =
          lpHaarDyadicCoefficient 𝕜 p m l (c • lpHaarDyadic 𝕜 p n k)
        rw [F.compression_coefficient 𝕜 p hp A B D hA hB, map_smul]
        by_cases hi : (⟨m, l⟩ : LpHaarTreeIndex) = ⟨n, k⟩
        · cases hi
          rw [LpHaarFiniteSplit.reader, LpHaarFiniteSplit.vector,
            lpHaarSignedBlockReader_multiplier 𝕜 p _ _ _ D _ (fun j => hD _ j),
            lpHaarDyadicCoefficient_apply_level, if_pos rfl, smul_eq_mul, mul_one]
          rfl
        · have hheap : lpHaarHeapIndex m l ≠ lpHaarHeapIndex n k :=
            fun h => hi (lpHaarHeapIndex_injective h)
          have hl : (F.node (lpHaarHeapIndex n k)).level ≠ (F.node (lpHaarHeapIndex m l)).level := by
            rcases lt_or_gt_of_ne hheap with h | h
            · exact (hlevels _ _ h).ne'
            · exact (hlevels _ _ h).ne
          rw [lpHaarFiniteSplit_reader_multiplier_other 𝕜 p hp _ _ hl D d hD]
          have hraw := lpHaarRaw_biorthogonal 𝕜 p hp (some ⟨m, l⟩) (some ⟨n, k⟩)
          simp only [Option.some.injEq, if_neg hi] at hraw
          change lpHaarDyadicCoefficient 𝕜 p m l (lpHaarDyadic 𝕜 p n k) = 0 at hraw
          change 0 = c • lpHaarDyadicCoefficient 𝕜 p m l (lpHaarDyadic 𝕜 p n k)
          rw [hraw, smul_zero]
  apply (intervalLpHaarBasis 𝕜 p hp).ext
  intro j
  change lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv j) _ =
    lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv j) _
  simp only [lpHaarNormalizedCoordinate, ContinuousLinearMap.smul_apply, hc]
  rfl

end LpHaarSequentialSplits
end ThesisCommon
