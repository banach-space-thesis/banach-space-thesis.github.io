import ThesisCommon.Analysis.LpHaarFaithfulRetractions

/-! Exact coefficients of the infinite reading operator and exact images
of Haar vectors under the infinite embedding. These identities connect
the measurable-tree retraction to the selected finite block matrices. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem lpHaarDyadicCoefficient_mean_zero (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicCoefficient 𝕜 p n k (lpHaarDyadicMean 𝕜 p hp n f) = 0 := by
  rw [← lpHaarLevelProjection_coefficient 𝕜 p n k,
    ← lpHaarDyadicMean_difference 𝕜 p hp n,
    lpHaarDyadicMean_adjacent_forward 𝕜 p hp n f,
    lpHaarDyadicMean_idempotent_apply 𝕜 p hp n f, sub_self, map_zero]

namespace LpHaarPartitionTree
variable (H : LpHaarPartitionTree)

theorem backward_fixed_mean (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp n (H.backward 𝕜 p hp n f) = H.backward 𝕜 p hp n f := by
  rw [H.backward_eq_sum_average 𝕜 p hp n f, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  congr 1
  exact lpHaarDyadicMean_fix_cell 𝕜 p hp n k k.isLt 1

theorem backward_coefficient_first (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicCoefficient 𝕜 p n k (H.backward 𝕜 p hp (n + 1) f) = H.nodeReader 𝕜 p n k f := by
  have hz : lpHaarDyadicCoefficient 𝕜 p n k (H.backward 𝕜 p hp n f) = 0 := by
    rw [← H.backward_fixed_mean 𝕜 p hp n f, lpHaarDyadicCoefficient_mean_zero]
  rw [H.backward_adjacent 𝕜 p hp n f, map_add, hz, zero_add, map_sum]
  simp only [map_smul, lpHaarDyadicCoefficient_apply_level, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem backward_coefficient (n : ℕ) (k : Fin (2 ^ n)) (m : ℕ) (hnm : n + 1 ≤ m)
    (f : IntervalLp 𝕜 p) :
    lpHaarDyadicCoefficient 𝕜 p n k (H.backward 𝕜 p hp m f) = H.nodeReader 𝕜 p n k f := by
  induction m, hnm using Nat.le_induction with
  | base => exact H.backward_coefficient_first 𝕜 p hp n k f
  | succ m hnm ih =>
      rw [H.backward_adjacent 𝕜 p hp m f, map_add, map_sum, ih]
      have hz : (∑ j : Fin (2 ^ m), lpHaarDyadicCoefficient 𝕜 p n k
          (H.nodeReader 𝕜 p m j f • lpHaarDyadic 𝕜 p m j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [map_smul, lpHaarDyadicCoefficient_other_level 𝕜 p hp m n j k (by omega), smul_zero]
      rw [hz, add_zero]

theorem reading_coefficient (A : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hA : ∀ f, Tendsto (fun m => H.backward 𝕜 p hp m f) atTop (𝓝 (A f)))
    (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicCoefficient 𝕜 p n k (A f) = H.nodeReader 𝕜 p n k f := by
  have hl := ((lpHaarDyadicCoefficient 𝕜 p n k).continuous.tendsto (A f)).comp (hA f)
  have hc : Tendsto (fun m => lpHaarDyadicCoefficient 𝕜 p n k (H.backward 𝕜 p hp m f))
      atTop (𝓝 (H.nodeReader 𝕜 p n k f)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with m hm
    exact (H.backward_coefficient 𝕜 p hp n k m hm f).symm
  exact tendsto_nhds_unique hl hc

theorem forward_stable_of_mean_fix (N : ℕ) (f : IntervalLp 𝕜 p)
    (hf : lpHaarDyadicMean 𝕜 p hp N f = f) :
    ∀ m ≥ N, H.forward 𝕜 p hp m f = H.forward 𝕜 p hp N f := by
  have hfix (m : ℕ) (hNm : N ≤ m) : lpHaarDyadicMean 𝕜 p hp m f = f := by
    calc
      _ = lpHaarDyadicMean 𝕜 p hp m (lpHaarDyadicMean 𝕜 p hp N f) := congrArg _ hf.symm
      _ = _ := (lpHaarDyadicMean_nested_forward 𝕜 p hp N m hNm f).trans hf
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      calc
        _ = H.forward 𝕜 p hp (m + 1) (lpHaarDyadicMean 𝕜 p hp m f) :=
          congrArg _ (hfix m hm).symm
        _ = _ := (H.forward_adjacent_mean 𝕜 p hp m f).trans ih

theorem forward_haar (n : ℕ) (k : Fin (2 ^ n)) :
    H.forward 𝕜 p hp (n + 1) (lpHaarDyadic 𝕜 p n k) = H.nodeVector 𝕜 p n k := by
  have hl := H.forward_cell 𝕜 p hp (n + 1) (lpHaarLeftIndex n k)
  have hr := H.forward_cell 𝕜 p hp (n + 1) (lpHaarRightIndex n k)
  change H.forward 𝕜 p hp (n + 1) (lpHaarCellVector 𝕜 p (n + 1) (2 * k.val)) = _ at hl
  change H.forward 𝕜 p hp (n + 1) (lpHaarCellVector 𝕜 p (n + 1) (2 * k.val + 1)) = _ at hr
  change H.forward 𝕜 p hp (n + 1)
    (lpHaarCellVector 𝕜 p (n + 1) (2 * k.val) - lpHaarCellVector 𝕜 p (n + 1) (2 * k.val + 1)) = _
  rw [map_sub, hl, hr]
  rfl

theorem embedding_haar (B : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hB : ∀ f, Tendsto (fun m => H.forward 𝕜 p hp m f) atTop (𝓝 (B f)))
    (n : ℕ) (k : Fin (2 ^ n)) : B (lpHaarDyadic 𝕜 p n k) = H.nodeVector 𝕜 p n k := by
  have hs := H.forward_stable_of_mean_fix 𝕜 p hp (n + 1) (lpHaarDyadic 𝕜 p n k)
    (lpHaarDyadicMean_fix_haar 𝕜 p hp n k k.isLt)
  have hc : Tendsto (fun m => H.forward 𝕜 p hp m (lpHaarDyadic 𝕜 p n k)) atTop
      (𝓝 (H.nodeVector 𝕜 p n k)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with m hm
    exact ((hs m hm).trans (H.forward_haar 𝕜 p hp n k)).symm
  exact tendsto_nhds_unique (hB _) hc

end LpHaarPartitionTree
end ThesisCommon
