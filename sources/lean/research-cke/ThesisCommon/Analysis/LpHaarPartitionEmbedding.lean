import ThesisCommon.Analysis.LpHaarPartitionTree
import ThesisCommon.Analysis.LpHaarSchauderBasis
import ThesisCommon.Analysis.SchauderStableOperatorLimit

/-! An actual isometric embedding associated with a measurable equal-mass
binary partition tree. Finite partition transports stabilise on Haar
polynomials, and their contractive strong limit preserves the Lp norm. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

theorem lpHaarPartitionStep_eq_smul {𝕜 α ι : Type*} [RCLike 𝕜]
    [MeasurableSpace α] [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure α} [IsFiniteMeasure μ] (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (a : ι → 𝕜) :
    lpHaarPartitionStep (p := p) (μ := μ) s hs a =
      ∑ i, a i • indicatorConstLp p (hs i) (measure_ne_top μ (s i)) (1 : 𝕜) := by
  unfold lpHaarPartitionStep
  apply Finset.sum_congr rfl
  intro i _
  exact lpHaarIndicator_smul (s i) (hs i) (a i)

variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem lpHaarDyadicMean_eq_sum_average (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp n f =
      ∑ k : Fin (2 ^ n), lpHaarPartitionAverage hp (lpHaarCell n k) f •
        lpHaarCellVector 𝕜 p n k := by
  change lpHaarPartitionMean hp _ _ _ _ _ f = _
  rw [lpHaarPartitionMean_eq_step, lpHaarPartitionStep_eq_smul]
  rfl

theorem lpHaarDyadicMean_eventually_fix_basis (j : ℕ) :
    ∃ N, ∀ n ≥ N, lpHaarDyadicMean 𝕜 p hp n
      ((intervalLpHaarBasis 𝕜 p hp).vector j) =
        (intervalLpHaarBasis 𝕜 p hp).vector j := by
  have hraw (i : Option (Σ n : ℕ, Fin (2 ^ n))) :
      ∃ N, ∀ n ≥ N, lpHaarDyadicMean 𝕜 p hp n (lpHaarRawVector 𝕜 p i) =
        lpHaarRawVector 𝕜 p i := by
    cases i with
    | none =>
        have hroot : lpHaarDyadicMean 𝕜 p hp 0 (lpHaarRawVector 𝕜 p none) =
            lpHaarRawVector 𝕜 p none := by
          rw [lpHaarDyadicMean_root]
          simp only [lpHaarRawCoordinate, lpHaarRawVector, lpHaarIntegral_const, one_smul]
        refine ⟨0, fun n hn => ?_⟩
        calc
          _ = lpHaarDyadicMean 𝕜 p hp n
              (lpHaarDyadicMean 𝕜 p hp 0 (lpHaarRawVector 𝕜 p none)) := congrArg _ hroot.symm
          _ = _ := (lpHaarDyadicMean_nested_forward 𝕜 p hp 0 n hn _).trans hroot
    | some i =>
        exact ⟨i.1 + 1, fun n hn =>
          lpHaarDyadicMean_fix_earlier_haar 𝕜 p hp i.1 n i.2 i.2.isLt (by omega)⟩
  obtain ⟨N, hN⟩ := hraw (lpHaarIndexEquiv j)
  refine ⟨N, fun n hn => ?_⟩
  change lpHaarDyadicMean 𝕜 p hp n (lpHaarNormalizedVector 𝕜 p _) = _
  rw [lpHaarNormalizedVector, map_smul, hN n hn]
  rfl

namespace LpHaarPartitionTree
variable (H : LpHaarPartitionTree)

theorem forward_parent (n : ℕ) (k : Fin (2 ^ n)) :
    H.forward 𝕜 p hp (n + 1) (lpHaarCellVector 𝕜 p n k) = H.cellVector 𝕜 p n k := by
  have hl := H.forward_cell 𝕜 p hp (n + 1) (lpHaarLeftIndex n k)
  have hr := H.forward_cell 𝕜 p hp (n + 1) (lpHaarRightIndex n k)
  change H.forward 𝕜 p hp (n + 1) (lpHaarCellVector 𝕜 p (n + 1) (2 * k.val)) = _ at hl
  change H.forward 𝕜 p hp (n + 1) (lpHaarCellVector 𝕜 p (n + 1) (2 * k.val + 1)) = _ at hr
  rw [lpHaarCellVector_split, map_add, hl, hr, ← H.cellVector_split]

theorem forward_eq_sum_average (n : ℕ) (f : IntervalLp 𝕜 p) :
    H.forward 𝕜 p hp n f =
      ∑ k : Fin (2 ^ n), lpHaarPartitionAverage hp (lpHaarCell n k) f •
        H.cellVector 𝕜 p n k := by
  rw [forward, lpHaarPartitionTransfer_apply, lpHaarPartitionStep_eq_smul]
  rfl

theorem forward_norm_eq_mean (n : ℕ) (f : IntervalLp 𝕜 p) :
    ‖H.forward 𝕜 p hp n f‖ = ‖lpHaarDyadicMean 𝕜 p hp n f‖ := by
  rw [forward, lpHaarPartitionTransfer_apply]
  change _ = ‖lpHaarPartitionMean hp _ _ _ _ _ f‖
  rw [lpHaarPartitionMean_eq_step]
  symm
  apply lpHaarPartitionStep_norm_eq hp _ _ (fun _ => measurableSet_Ioc)
    (H.measurable n) (lpHaarLevelCells_disjoint n) (H.disjoint n)
    (lpHaarLevelCells_cover n) (H.cover n)
  intro k
  exact (lpHaarCell_measure n k k.isLt).trans (H.measure n k).symm

theorem forward_adjacent_mean (n : ℕ) (f : IntervalLp 𝕜 p) :
    H.forward 𝕜 p hp (n + 1) (lpHaarDyadicMean 𝕜 p hp n f) =
      H.forward 𝕜 p hp n f := by
  rw [lpHaarDyadicMean_eq_sum_average 𝕜 p hp n f, map_sum,
    H.forward_eq_sum_average 𝕜 p hp n f]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, H.forward_parent 𝕜 p hp n k]

theorem forward_stable_basis (j : ℕ) :
    ∃ N, ∀ n ≥ N, H.forward 𝕜 p hp n ((intervalLpHaarBasis 𝕜 p hp).vector j) =
      H.forward 𝕜 p hp N ((intervalLpHaarBasis 𝕜 p hp).vector j) := by
  obtain ⟨N, hN⟩ := lpHaarDyadicMean_eventually_fix_basis 𝕜 p hp j
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      calc
        _ = H.forward 𝕜 p hp (n + 1)
            (lpHaarDyadicMean 𝕜 p hp n ((intervalLpHaarBasis 𝕜 p hp).vector j)) :=
              congrArg _ (hN n hn).symm
        _ = H.forward 𝕜 p hp n ((intervalLpHaarBasis 𝕜 p hp).vector j) :=
          H.forward_adjacent_mean 𝕜 p hp n _
        _ = _ := ih

theorem exists_embedding :
    ∃ B : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p,
      ‖B‖ ≤ 1 ∧ (∀ f, ‖B f‖ = ‖f‖) ∧
        ∀ f, Tendsto (fun n => H.forward 𝕜 p hp n f) atTop (𝓝 (B f)) := by
  obtain ⟨B, hB, hlim⟩ := (intervalLpHaarBasis 𝕜 p hp).exists_operator_of_stable_basis
    (H.forward 𝕜 p hp) zero_le_one (H.forward_norm_le 𝕜 p hp)
    (H.forward_stable_basis 𝕜 p hp)
  refine ⟨B, hB, fun f => ?_, hlim⟩
  have hn := (lpHaarDyadicMean_tendsto 𝕜 p hp f).norm
  have heq : (fun n => ‖lpHaarDyadicMean 𝕜 p hp n f‖) =
      (fun n => ‖H.forward 𝕜 p hp n f‖) :=
    funext (fun n => (H.forward_norm_eq_mean 𝕜 p hp n f).symm)
  rw [heq] at hn
  exact tendsto_nhds_unique (hlim f).norm hn

end LpHaarPartitionTree
end ThesisCommon
