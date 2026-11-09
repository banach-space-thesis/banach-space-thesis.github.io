import ThesisCommon.Analysis.LpHaarPartitionMean
import ThesisCommon.Analysis.LpHaarDyadic
import Mathlib.Order.Interval.Set.Union

/-! Contractive dyadic averaging operators in the genuine interval Lp spaces. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical Function
namespace ThesisCommon

theorem lpHaarLevelCells_union (n : ℕ) :
    (⋃ k : Fin (2 ^ n), lpHaarCell n k) = Ioc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    have hnonneg : 0 ≤ (k.val : ℝ) * intervalLpDyadicRadius n :=
      mul_nonneg (Nat.cast_nonneg _) (intervalLpDyadicRadius_pos n).le
    exact ⟨hnonneg.trans_lt hk.1, (lpHaarCell_subset n k k.isLt hk).2⟩
  · intro x hx
    have hx' : x ∈ Ioc ((0 : ℕ) * intervalLpDyadicRadius n)
        (((2 ^ n : ℕ) : ℝ) * intervalLpDyadicRadius n) := by
      simpa only [Nat.cast_zero, zero_mul, lpHaarRadius_cancel] using hx
    have h := Ioc_subset_biUnion_Ioc (2 ^ n)
      (fun k : ℕ => (k : ℝ) * intervalLpDyadicRadius n) hx'
    obtain ⟨k, h⟩ := mem_iUnion.mp h
    obtain ⟨hk, h⟩ := mem_iUnion.mp h
    apply mem_iUnion.mpr
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, ?_⟩
    simpa only [lpHaarCell, Nat.cast_add, Nat.cast_one] using h

theorem lpHaarLevelCells_cover (n : ℕ) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ ⋃ k : Fin (2 ^ n), lpHaarCell n k := by
  rw [lpHaarLevelCells_union]
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℝ)))] with x hx hzero
  exact ⟨lt_of_le_of_ne hx.1 (by simpa [eq_comm] using hzero), hx.2⟩

theorem lpHaarLevelCells_disjoint (n : ℕ) :
    Pairwise (fun k j : Fin (2 ^ n) => Disjoint (lpHaarCell n k) (lpHaarCell n j)) := by
  intro k j hkj
  exact lpHaarCell_disjoint_sameLevel n (fun h => hkj (Fin.ext h))

theorem lpHaarLevelCells_nonzero (n : ℕ) (k : Fin (2 ^ n)) :
    (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarCell n k) ≠ 0 := by
  rw [lpHaarCell_measure n k k.isLt]
  exact (ENNReal.ofReal_pos.mpr (intervalLpDyadicRadius_pos n)).ne'

def lpHaarDyadicMean (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  lpHaarPartitionMean hp (fun k : Fin (2 ^ n) => lpHaarCell n k)
    (fun _ => measurableSet_Ioc) (lpHaarLevelCells_disjoint n) (lpHaarLevelCells_cover n)
    (lpHaarLevelCells_nonzero n)

theorem lpHaarDyadicMean_norm_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) : ‖lpHaarDyadicMean 𝕜 p hp n‖ ≤ 1 :=
  norm_lpHaarPartitionMean_le hp (fun k : Fin (2 ^ n) => lpHaarCell n k)
    (fun _ => measurableSet_Ioc) (lpHaarLevelCells_disjoint n) (lpHaarLevelCells_cover n)
    (lpHaarLevelCells_nonzero n)

theorem lpHaarDyadicMean_idempotent (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) :
    (lpHaarDyadicMean 𝕜 p hp n).comp (lpHaarDyadicMean 𝕜 p hp n) = lpHaarDyadicMean 𝕜 p hp n :=
  lpHaarPartitionMean_idempotent hp (fun k : Fin (2 ^ n) => lpHaarCell n k)
    (fun _ => measurableSet_Ioc) (lpHaarLevelCells_disjoint n) (lpHaarLevelCells_cover n)
    (lpHaarLevelCells_nonzero n)

theorem lpHaarDyadicMean_coordinate (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (f : IntervalLp 𝕜 p) (k : Fin (2 ^ n)) :
    lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarDyadicMean 𝕜 p hp n f) =
      lpHaarMean hp (lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) f) :=
  lpHaarPartitionMean_coordinate hp (fun k : Fin (2 ^ n) => lpHaarCell n k)
    (fun _ => measurableSet_Ioc) (lpHaarLevelCells_disjoint n) (lpHaarLevelCells_cover n)
    (lpHaarLevelCells_nonzero n) f k

end ThesisCommon
