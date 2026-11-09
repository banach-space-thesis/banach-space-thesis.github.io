import ThesisCommon.Analysis.LpHaarPartitionEmbedding
import ThesisCommon.Analysis.LpHaarBinarySums
import ThesisCommon.Analysis.LpHaarCoefficientFormula

/-! Exact finite reading identities for measured binary Haar trees.
The difference of adjacent reading maps is the tree's genuine Haar
coefficient expansion at one level. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

theorem lpHaarPartitionAverage_setIntegral {𝕜 α : Type*} [RCLike 𝕜]
    [MeasurableSpace α] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}
    [IsFiniteMeasure μ] (hp : p ≠ ∞) (s : Set α) (f : Lp 𝕜 p μ) :
    lpHaarPartitionAverage hp s f = (μ.real s : 𝕜)⁻¹ * ∫ x in s, f x ∂μ := by
  rw [lpHaarPartitionAverage_apply,
    integral_congr_ae (lebesgueLpRestrict_coe (𝕜 := 𝕜) s f)]

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

namespace LpHaarPartitionTree
variable (H : LpHaarPartitionTree) (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

def nodeVector (n : ℕ) (k : Fin (2 ^ n)) : IntervalLp 𝕜 p :=
  H.cellVector 𝕜 p (n + 1) (lpHaarLeftIndex n k) -
    H.cellVector 𝕜 p (n + 1) (lpHaarRightIndex n k)

def nodeReader (n : ℕ) (k : Fin (2 ^ n)) : IntervalLp 𝕜 p →L[𝕜] 𝕜 :=
  lpHaarCoefficient (H.cell (n + 1) (lpHaarLeftIndex n k))
    (H.cell (n + 1) (lpHaarRightIndex n k))
    (H.measurable (n + 1) (lpHaarLeftIndex n k))
    (H.measurable (n + 1) (lpHaarRightIndex n k))
    (H.disjoint (n + 1) (lpHaar_child_indices_ne n k))

theorem average_apply (hp : p.val ≠ ∞) (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    lpHaarPartitionAverage hp (H.cell n k) f = (intervalLpDyadicRadius n : 𝕜)⁻¹ *
      ∫ x in H.cell n k, f x ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [lpHaarPartitionAverage_setIntegral, measureReal_def, H.measure,
    ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]

theorem nodeReader_apply (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    H.nodeReader 𝕜 p n k f = (intervalLpDyadicRadius n : 𝕜)⁻¹ *
      ((∫ x in H.cell (n + 1) (lpHaarLeftIndex n k), f x
        ∂(volume.restrict (Icc (0 : ℝ) 1))) -
        ∫ x in H.cell (n + 1) (lpHaarRightIndex n k), f x
          ∂(volume.restrict (Icc (0 : ℝ) 1))) := by
  rw [nodeReader, lpHaarCoefficient_apply_integrals, H.split, measureReal_def, H.measure,
    ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]

theorem nodeReader_self (n : ℕ) (k : Fin (2 ^ n)) :
    H.nodeReader 𝕜 p n k (H.nodeVector 𝕜 p n k) = 1 := by
  apply lpHaarCoefficient_self
  rw [H.split]
  exact H.cell_nonzero n k

theorem average_children (hp : p.val ≠ ∞) (n : ℕ) (k : Fin (2 ^ n))
    (f : IntervalLp 𝕜 p) :
    lpHaarPartitionAverage hp (H.cell n k) f = (1 / 2 : 𝕜) *
      (lpHaarPartitionAverage hp (H.cell (n + 1) (lpHaarLeftIndex n k)) f +
        lpHaarPartitionAverage hp (H.cell (n + 1) (lpHaarRightIndex n k)) f) := by
  have hu := setIntegral_union (H.disjoint (n + 1) (lpHaar_child_indices_ne n k))
    (H.measurable (n + 1) (lpHaarRightIndex n k))
    ((Lp.memLp f).integrable Fact.out).integrableOn
    ((Lp.memLp f).integrable Fact.out).integrableOn
  rw [H.split] at hu
  rw [H.average_apply 𝕜 p hp, H.average_apply 𝕜 p hp,
    H.average_apply 𝕜 p hp, hu, lpHaarRadius_succ]
  push_cast
  have hr : (intervalLpDyadicRadius n : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne'
  field_simp
  <;> ring

theorem nodeReader_eq_half_average_difference (hp : p.val ≠ ∞) (n : ℕ)
    (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    H.nodeReader 𝕜 p n k f = (1 / 2 : 𝕜) *
      (lpHaarPartitionAverage hp (H.cell (n + 1) (lpHaarLeftIndex n k)) f -
        lpHaarPartitionAverage hp (H.cell (n + 1) (lpHaarRightIndex n k)) f) := by
  rw [H.nodeReader_apply, H.average_apply 𝕜 p hp,
    H.average_apply 𝕜 p hp, lpHaarRadius_succ]
  push_cast
  field_simp
  <;> ring

theorem backward_eq_sum_average (hp : p.val ≠ ∞) (n : ℕ) (f : IntervalLp 𝕜 p) :
    H.backward 𝕜 p hp n f =
      ∑ k : Fin (2 ^ n), lpHaarPartitionAverage hp (H.cell n k) f •
        lpHaarCellVector 𝕜 p n k := by
  rw [backward, lpHaarPartitionTransfer_apply, lpHaarPartitionStep_eq_smul]
  rfl

theorem backward_forward (hp : p.val ≠ ∞) (n : ℕ) (f : IntervalLp 𝕜 p) :
    H.backward 𝕜 p hp n (H.forward 𝕜 p hp n f) = lpHaarDyadicMean 𝕜 p hp n f := by
  rw [H.forward_eq_sum_average 𝕜 p hp n f, map_sum,
    lpHaarDyadicMean_eq_sum_average 𝕜 p hp n f]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, H.backward_cell 𝕜 p hp n k]

theorem backward_adjacent (hp : p.val ≠ ∞) (n : ℕ) (f : IntervalLp 𝕜 p) :
    H.backward 𝕜 p hp (n + 1) f = H.backward 𝕜 p hp n f +
      ∑ k : Fin (2 ^ n), H.nodeReader 𝕜 p n k f • lpHaarDyadic 𝕜 p n k := by
  rw [H.backward_eq_sum_average 𝕜 p hp (n + 1) f, lpHaar_sum_children,
    H.backward_eq_sum_average 𝕜 p hp n f, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  change _ • lpHaarCellVector 𝕜 p (n + 1) (2 * k.val) +
    _ • lpHaarCellVector 𝕜 p (n + 1) (2 * k.val + 1) = _
  rw [lpHaarCellVector_left, lpHaarCellVector_right,
    H.average_children 𝕜 p hp n k f, H.nodeReader_eq_half_average_difference 𝕜 p hp n k f]
  module

end LpHaarPartitionTree
end ThesisCommon
