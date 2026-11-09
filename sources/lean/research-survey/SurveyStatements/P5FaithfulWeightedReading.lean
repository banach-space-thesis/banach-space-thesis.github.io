import SurveyStatements.P5Support.LpHaarBlockCompression

/-! An actual faithful reading map sends a weighted selected block to the
arithmetic mean of its weights times the corresponding original Haar vector. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5Support
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

def lpHaarWeightedSplitVector (S : LpHaarFiniteSplit)
    (c : Fin (2 ^ S.level) → 𝕜) : IntervalLp 𝕜 p :=
  ∑ j ∈ S.atoms, signedValue (S.signs j) (c j • lpHaarDyadic 𝕜 p S.level j)

theorem lpHaarWeightedSplitVector_coefficient (S : LpHaarFiniteSplit)
    (c : Fin (2 ^ S.level) → 𝕜) (k : Fin (2 ^ S.level)) :
    lpHaarDyadicCoefficient 𝕜 p S.level k (lpHaarWeightedSplitVector 𝕜 p S c) =
      if k ∈ S.atoms then signedValue (S.signs k) (c k) else 0 := by
  rw [lpHaarWeightedSplitVector, map_sum]
  have hterm (j : Fin (2 ^ S.level)) :
      lpHaarDyadicCoefficient 𝕜 p S.level k
        (signedValue (S.signs j) (c j • lpHaarDyadic 𝕜 p S.level j)) =
          if k = j then signedValue (S.signs j) (c j) else 0 := by
    by_cases hkj : k = j <;> cases S.signs j <;>
      simp [signedValue, map_smul, lpHaarDyadicCoefficient_apply_level, hkj]
  simp_rw [hterm]
  simp [Finset.sum_ite_eq]

theorem lpHaarWeightedSplitVector_reader_self (S : LpHaarFiniteSplit)
    (c : Fin (2 ^ S.level) → 𝕜) :
    S.reader 𝕜 p (lpHaarWeightedSplitVector 𝕜 p S c) =
      (S.atoms.card : 𝕜)⁻¹ * ∑ j ∈ S.atoms, c j := by
  rw [LpHaarFiniteSplit.reader, lpHaarSignedBlockReader_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [lpHaarWeightedSplitVector_coefficient, if_pos hj, signedValue_self]

theorem lpHaarWeightedSplitVector_integral (S : LpHaarFiniteSplit)
    (c : Fin (2 ^ S.level) → 𝕜) :
    lpHaarIntegral (lpHaarWeightedSplitVector 𝕜 p S c) = 0 := by
  rw [lpHaarWeightedSplitVector, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  cases S.signs j <;> simp only [signedValue, if_true, Bool.false_eq_true, if_false,
    map_neg, map_smul, lpHaarIntegral_apply, lpHaarDyadic_integral_zero 𝕜 p S.level j j.isLt,
    smul_zero, neg_zero]

theorem lpHaarWeightedSplitVector_reader_other (hp : p.val ≠ ∞)
    (S R : LpHaarFiniteSplit) (hlevel : R.level ≠ S.level)
    (c : Fin (2 ^ R.level) → 𝕜) :
    S.reader 𝕜 p (lpHaarWeightedSplitVector 𝕜 p R c) = 0 := by
  rw [LpHaarFiniteSplit.reader, lpHaarSignedBlockReader_apply]
  have hz (k : Fin (2 ^ S.level)) :
      lpHaarDyadicCoefficient 𝕜 p S.level k (lpHaarWeightedSplitVector 𝕜 p R c) = 0 := by
    rw [lpHaarWeightedSplitVector, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    cases R.signs j <;> simp only [signedValue, if_true, Bool.false_eq_true, if_false,
      map_neg, map_smul,
      lpHaarDyadicCoefficient_other_level 𝕜 p hp R.level S.level j k hlevel.symm,
      smul_zero, neg_zero]
  simp_rw [hz]
  have hzero (k : Fin (2 ^ S.level)) : signedValue (S.signs k) (0 : 𝕜) = 0 := by
    cases S.signs k <;> simp [signedValue]
  simp_rw [hzero]
  simp

theorem LpHaarSequentialSplits.reading_weighted_block (hp : p.val ≠ ∞)
    (F : LpHaarSequentialSplits)
    (hlevels : ∀ i j, i < j → (F.node i).level < (F.node j).level)
    (A : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hA : ∀ f, Tendsto (fun m => F.toPartitionTree.backward 𝕜 p hp m f) atTop (𝓝 (A f)))
    (n : ℕ) (k : Fin (2 ^ n))
    (c : Fin (2 ^ (F.node (lpHaarHeapIndex n k)).level) → 𝕜) :
    A (lpHaarWeightedSplitVector 𝕜 p (F.node (lpHaarHeapIndex n k)) c) =
      (((F.node (lpHaarHeapIndex n k)).atoms.card : 𝕜)⁻¹ *
        (∑ j ∈ (F.node (lpHaarHeapIndex n k)).atoms, c j)) • lpHaarDyadic 𝕜 p n k := by
  let R := F.node (lpHaarHeapIndex n k)
  let a := (R.atoms.card : 𝕜)⁻¹ * ∑ j ∈ R.atoms, c j
  have hc : ∀ i : Option LpHaarTreeIndex,
      lpHaarRawCoordinate 𝕜 p i (A (lpHaarWeightedSplitVector 𝕜 p R c)) =
        lpHaarRawCoordinate 𝕜 p i (a • lpHaarDyadic 𝕜 p n k) := by
    intro i
    cases i with
    | none =>
        change lpHaarIntegral (A (lpHaarWeightedSplitVector 𝕜 p R c)) =
          lpHaarIntegral (a • lpHaarDyadic 𝕜 p n k)
        rw [F.toPartitionTree.reading_integral 𝕜 p hp A hA,
          lpHaarWeightedSplitVector_integral, map_smul, lpHaarIntegral_apply,
          lpHaarDyadic_integral_zero 𝕜 p n k k.isLt, smul_zero]
    | some i =>
        rcases i with ⟨m, l⟩
        change lpHaarDyadicCoefficient 𝕜 p m l (A (lpHaarWeightedSplitVector 𝕜 p R c)) =
          lpHaarDyadicCoefficient 𝕜 p m l (a • lpHaarDyadic 𝕜 p n k)
        rw [F.toPartitionTree.reading_coefficient 𝕜 p hp A hA,
          F.nodeReader_eq 𝕜 p, map_smul]
        by_cases hi : (⟨m, l⟩ : LpHaarTreeIndex) = ⟨n, k⟩
        · cases hi
          rw [lpHaarWeightedSplitVector_reader_self,
            lpHaarDyadicCoefficient_apply_level, if_pos rfl, smul_eq_mul, mul_one]
        · have hheap : lpHaarHeapIndex m l ≠ lpHaarHeapIndex n k :=
            fun h => hi (lpHaarHeapIndex_injective h)
          have hl : R.level ≠ (F.node (lpHaarHeapIndex m l)).level := by
            rcases lt_or_gt_of_ne hheap with h | h
            · exact (hlevels _ _ h).ne'
            · exact (hlevels _ _ h).ne
          rw [lpHaarWeightedSplitVector_reader_other 𝕜 p hp _ _ hl]
          have hraw := lpHaarRaw_biorthogonal 𝕜 p hp (some ⟨m, l⟩) (some ⟨n, k⟩)
          simp only [Option.some.injEq, if_neg hi] at hraw
          change lpHaarDyadicCoefficient 𝕜 p m l (lpHaarDyadic 𝕜 p n k) = 0 at hraw
          change 0 = a • lpHaarDyadicCoefficient 𝕜 p m l (lpHaarDyadic 𝕜 p n k)
          rw [hraw, smul_zero]
  apply (intervalLpHaarBasis 𝕜 p hp).ext
  intro j
  change lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv j)
    (A (lpHaarWeightedSplitVector 𝕜 p R c)) =
      lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv j) (a • lpHaarDyadic 𝕜 p n k)
  simp only [lpHaarNormalizedCoordinate, ContinuousLinearMap.smul_apply]
  rw [hc]

end SurveyStatements.P5Support
