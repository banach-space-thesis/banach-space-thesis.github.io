import ThesisCommon.Analysis.LpPartitionTransfer
import ThesisCommon.Analysis.LpHaarSignedChildIndices

/-! Measurable binary partition trees with the actual dyadic atom measures.
The finite embedding and reading maps are constructed by contractive
partition transfer. Their bounds are consequences of the measured geometry. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

def lpHaarLeftIndex (n : ℕ) : Fin (2 ^ n) ↪ Fin (2 ^ (n + 1)) :=
  lpHaarSignedChildIndex n (fun _ => true)

def lpHaarRightIndex (n : ℕ) : Fin (2 ^ n) ↪ Fin (2 ^ (n + 1)) :=
  lpHaarSignedChildIndex n (fun _ => false)

structure LpHaarPartitionTree where
  cell : (n : ℕ) → Fin (2 ^ n) → Set ℝ
  measurable : ∀ n k, MeasurableSet (cell n k)
  disjoint : ∀ n, Pairwise (fun i j => Disjoint (cell n i) (cell n j))
  cover : ∀ n, ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ ⋃ k, cell n k
  measure : ∀ n k, (volume.restrict (Icc (0 : ℝ) 1)) (cell n k) =
    ENNReal.ofReal (intervalLpDyadicRadius n)
  split : ∀ n k, cell (n + 1) (lpHaarLeftIndex n k) ∪
    cell (n + 1) (lpHaarRightIndex n k) = cell n k

namespace LpHaarPartitionTree

def standard : LpHaarPartitionTree where
  cell n k := lpHaarCell n k
  measurable _ _ := measurableSet_Ioc
  disjoint := lpHaarLevelCells_disjoint
  cover := lpHaarLevelCells_cover
  measure n k := lpHaarCell_measure n k k.isLt
  split n k := lpHaarCell_children n k

variable (H : LpHaarPartitionTree) (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

theorem cell_nonzero (n : ℕ) (k : Fin (2 ^ n)) :
    (volume.restrict (Icc (0 : ℝ) 1)) (H.cell n k) ≠ 0 := by
  rw [H.measure]
  exact (ENNReal.ofReal_pos.mpr (intervalLpDyadicRadius_pos n)).ne'

def cellVector (n : ℕ) (k : Fin (2 ^ n)) : IntervalLp 𝕜 p :=
  indicatorConstLp p.val (H.measurable n k)
    (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) (1 : 𝕜)

theorem cellVector_split (n : ℕ) (k : Fin (2 ^ n)) :
    H.cellVector 𝕜 p n k = H.cellVector 𝕜 p (n + 1) (lpHaarLeftIndex n k) +
      H.cellVector 𝕜 p (n + 1) (lpHaarRightIndex n k) := by
  have hne : lpHaarLeftIndex n k ≠ lpHaarRightIndex n k := by
    intro h
    have hv := congrArg Fin.val h
    change 2 * k.val + 0 = 2 * k.val + 1 at hv
    omega
  have h := indicatorConstLp_disjoint_union (p := p.val)
    (H.measurable (n + 1) (lpHaarLeftIndex n k))
    (H.measurable (n + 1) (lpHaarRightIndex n k))
    (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _)
    (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _)
    (H.disjoint (n + 1) hne) (1 : 𝕜)
  simpa only [H.split, cellVector] using h

def forward (hp : p.val ≠ ∞) (n : ℕ) : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  lpHaarPartitionTransfer hp (fun k : Fin (2 ^ n) => lpHaarCell n k)
    (H.cell n) (H.measurable n)

def backward (hp : p.val ≠ ∞) (n : ℕ) : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  lpHaarPartitionTransfer hp (H.cell n) (fun k : Fin (2 ^ n) => lpHaarCell n k)
    (fun _ => measurableSet_Ioc)

theorem forward_norm_le (hp : p.val ≠ ∞) (n : ℕ) : ‖H.forward 𝕜 p hp n‖ ≤ 1 := by
  apply lpHaarPartitionTransfer_norm_le hp _ _ (fun _ => measurableSet_Ioc)
    (H.measurable n) (lpHaarLevelCells_disjoint n) (H.disjoint n)
    (lpHaarLevelCells_cover n) (H.cover n) (lpHaarLevelCells_nonzero n)
  intro k
  change (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarCell n k) = _
  rw [lpHaarCell_measure n k k.isLt, H.measure]

theorem backward_norm_le (hp : p.val ≠ ∞) (n : ℕ) : ‖H.backward 𝕜 p hp n‖ ≤ 1 := by
  apply lpHaarPartitionTransfer_norm_le hp _ _ (H.measurable n)
    (fun _ => measurableSet_Ioc) (H.disjoint n) (lpHaarLevelCells_disjoint n)
    (H.cover n) (lpHaarLevelCells_cover n) (H.cell_nonzero n)
  intro k
  change _ = (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarCell n k)
  rw [lpHaarCell_measure n k k.isLt, H.measure]

theorem forward_cell (hp : p.val ≠ ∞) (n : ℕ) (k : Fin (2 ^ n)) :
    H.forward 𝕜 p hp n (lpHaarCellVector 𝕜 p n k) = H.cellVector 𝕜 p n k :=
  lpHaarPartitionTransfer_indicator hp _ _ (fun _ => measurableSet_Ioc)
    (H.measurable n) (lpHaarLevelCells_disjoint n) (lpHaarLevelCells_nonzero n) k 1

theorem backward_cell (hp : p.val ≠ ∞) (n : ℕ) (k : Fin (2 ^ n)) :
    H.backward 𝕜 p hp n (H.cellVector 𝕜 p n k) = lpHaarCellVector 𝕜 p n k :=
  lpHaarPartitionTransfer_indicator hp _ _ (H.measurable n)
    (fun _ => measurableSet_Ioc) (H.disjoint n) (H.cell_nonzero n) k 1

end LpHaarPartitionTree
end ThesisCommon
