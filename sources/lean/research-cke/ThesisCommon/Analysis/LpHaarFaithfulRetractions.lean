import ThesisCommon.Analysis.LpHaarPartitionReaders
import ThesisCommon.Analysis.LpHaarSignedReaderFormula

/-! A geometrically faithful binary tree gives actual contractive
embedding and reading operators with an exact left inverse. Faithfulness
here is an equality of measurable child sets with finite signed dyadic
blocks at levels tending to infinity, not a factorisation assumption. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

theorem lpHaarCoefficient_congr_sets {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsProbabilityMeasure μ]
    {s t s' t' : Set α} {hs : MeasurableSet s} {ht : MeasurableSet t}
    {hs' : MeasurableSet s'} {ht' : MeasurableSet t'}
    {hd : Disjoint s t} {hd' : Disjoint s' t'} (he : s = s') (he' : t = t') :
    lpHaarCoefficient (𝕜 := 𝕜) (p := p) (μ := μ) s t hs ht hd =
      lpHaarCoefficient s' t' hs' ht' hd' := by
  subst s'
  subst t'
  rfl

namespace LpHaarPartitionTree

def FaithfulSplits (H : LpHaarPartitionTree) : Prop :=
  ∀ n k, ∃ (r : ℕ) (S : Finset (Fin (2 ^ r))) (θ : Fin (2 ^ r) → Bool), n ≤ r ∧
    H.cell (n + 1) (lpHaarLeftIndex n k) = lpHaarSignedPart r S θ ∧
    H.cell (n + 1) (lpHaarRightIndex n k) = lpHaarSignedPart r S (fun j => !(θ j))

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (H : LpHaarPartitionTree) (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

theorem nodeReader_const (n : ℕ) (k : Fin (2 ^ n)) (c : 𝕜) :
    H.nodeReader 𝕜 p n k (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) c) = 0 := by
  apply lpHaarCoefficient_constant_on
    (H.cell (n + 1) (lpHaarLeftIndex n k))
    (H.cell (n + 1) (lpHaarRightIndex n k))
    (H.measurable (n + 1) (lpHaarLeftIndex n k))
    (H.measurable (n + 1) (lpHaarRightIndex n k))
    (H.disjoint (n + 1) (lpHaar_child_indices_ne n k))
    (by rw [H.measure, H.measure]) _ c
  filter_upwards [Lp.coeFn_const p.val (volume.restrict (Icc (0 : ℝ) 1)) c] with x hx
  exact fun _ => hx

theorem nodeReader_signed (n : ℕ) (k : Fin (2 ^ n))
    (r : ℕ) (S : Finset (Fin (2 ^ r))) (θ : Fin (2 ^ r) → Bool)
    (hl : H.cell (n + 1) (lpHaarLeftIndex n k) = lpHaarSignedPart r S θ)
    (hr : H.cell (n + 1) (lpHaarRightIndex n k) = lpHaarSignedPart r S (fun j => !(θ j))) :
    H.nodeReader 𝕜 p n k = lpHaarSignedBlockReader 𝕜 p r S θ := by
  rw [nodeReader, lpHaarSignedBlockReader_eq_coefficient]
  exact lpHaarCoefficient_congr_sets hl hr

variable (hp : p.val ≠ ∞)

include hp in
theorem faithful_reader_kill_earlier (hH : H.FaithfulSplits)
    (n : ℕ) (k : Fin (2 ^ n)) (m : ℕ) (j : Fin (2 ^ m)) (hmn : m < n) :
    H.nodeReader 𝕜 p n k (lpHaarDyadic 𝕜 p m j) = 0 := by
  obtain ⟨r, S, θ, hnr, hl, hr⟩ := hH n k
  rw [H.nodeReader_signed 𝕜 p n k r S θ hl hr, lpHaarSignedBlockReader_apply]
  have hz : (∑ i ∈ S, signedValue (θ i)
      (lpHaarDyadicCoefficient 𝕜 p r i (lpHaarDyadic 𝕜 p m j))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [lpHaarDyadicCoefficient_other_level 𝕜 p hp m r j i (by omega)]
    cases θ i <;> simp [signedValue]
  rw [hz, mul_zero]

theorem faithful_readers_escape (hH : H.FaithfulSplits) (j : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ k : Fin (2 ^ n),
      H.nodeReader 𝕜 p n k ((intervalLpHaarBasis 𝕜 p hp).vector j) = 0 := by
  cases he : lpHaarIndexEquiv j with
  | none =>
      refine ⟨0, fun n _ k => ?_⟩
      change H.nodeReader 𝕜 p n k (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv j)) = 0
      rw [he, lpHaarNormalizedVector, map_smul]
      simp only [lpHaarRawVector, H.nodeReader_const, smul_zero]
  | some i =>
      rcases i with ⟨m, l⟩
      refine ⟨m + 1, fun n hn k => ?_⟩
      change H.nodeReader 𝕜 p n k (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv j)) = 0
      rw [he, lpHaarNormalizedVector, map_smul]
      change _ • H.nodeReader 𝕜 p n k (lpHaarDyadic 𝕜 p m l) = 0
      rw [H.faithful_reader_kill_earlier 𝕜 p hp hH n k m l (by omega), smul_zero]

theorem faithful_backward_stable_basis (hH : H.FaithfulSplits) (j : ℕ) :
    ∃ N, ∀ n ≥ N, H.backward 𝕜 p hp n ((intervalLpHaarBasis 𝕜 p hp).vector j) =
      H.backward 𝕜 p hp N ((intervalLpHaarBasis 𝕜 p hp).vector j) := by
  obtain ⟨N, hN⟩ := H.faithful_readers_escape 𝕜 p hp hH j
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have hz : (∑ k : Fin (2 ^ n), H.nodeReader 𝕜 p n k
          ((intervalLpHaarBasis 𝕜 p hp).vector j) • lpHaarDyadic 𝕜 p n k) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [hN n hn k, zero_smul]
      rw [H.backward_adjacent 𝕜 p hp n _, hz, add_zero, ih]

theorem exists_faithful_retraction (hH : H.FaithfulSplits) :
    ∃ A B : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ A.comp B = ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) ∧
        (∀ f, ‖B f‖ = ‖f‖) ∧
        (∀ f, Tendsto (fun n => H.backward 𝕜 p hp n f) atTop (𝓝 (A f))) ∧
        (∀ f, Tendsto (fun n => H.forward 𝕜 p hp n f) atTop (𝓝 (B f))) := by
  obtain ⟨B, hB, hiso, hBlim⟩ := H.exists_embedding 𝕜 p hp
  obtain ⟨A, hA, hAlim⟩ := (intervalLpHaarBasis 𝕜 p hp).exists_operator_of_stable_basis
    (H.backward 𝕜 p hp) zero_le_one (H.backward_norm_le 𝕜 p hp)
    (H.faithful_backward_stable_basis 𝕜 p hp hH)
  refine ⟨A, B, hA, hB, ?_, hiso, hAlim, hBlim⟩
  apply (intervalLpHaarBasis 𝕜 p hp).operator_ext
  intro j
  let v := (intervalLpHaarBasis 𝕜 p hp).vector j
  obtain ⟨N, hN⟩ := H.forward_stable_basis 𝕜 p hp j
  have hb : Tendsto (fun n => H.forward 𝕜 p hp n v) atTop
      (𝓝 (H.forward 𝕜 p hp N v)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (hN n hn).symm
  have hBv : B v = H.forward 𝕜 p hp N v := tendsto_nhds_unique (hBlim v) hb
  obtain ⟨M, hM⟩ := lpHaarDyadicMean_eventually_fix_basis 𝕜 p hp j
  have ha : Tendsto (fun n => H.backward 𝕜 p hp n (B v)) atTop (𝓝 v) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max N M)] with n hn
    have hforward : H.forward 𝕜 p hp n v = B v :=
      (hN n ((le_max_left N M).trans hn)).trans hBv.symm
    have hback : H.backward 𝕜 p hp n (B v) = v := by
      rw [← hforward, H.backward_forward 𝕜 p hp n v]
      exact hM n ((le_max_right N M).trans hn)
    exact hback.symm
  exact tendsto_nhds_unique (hAlim (B v)) ha

end LpHaarPartitionTree
end ThesisCommon
