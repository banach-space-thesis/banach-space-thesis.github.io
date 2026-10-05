import ThesisCommon.Analysis.LpHaarRetractionCoefficients
import ThesisCommon.Analysis.LpMeanZeroHaarBasis

/-! The actual Haar-tree retraction preserves the integral and therefore
restricts to a contractive retraction of the genuine mean-zero Lp space. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
namespace LpHaarPartitionTree
variable (H : LpHaarPartitionTree) (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

theorem root_cell_ae :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ H.cell 0 ⟨0, by decide⟩ := by
  filter_upwards [H.cover 0] with x hx
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  have hk0 : k = ⟨0, by decide⟩ := by
    apply Fin.ext
    have h := k.isLt
    simp only [pow_zero] at h
    omega
  simpa only [hk0] using hk

theorem root_vector_const : H.cellVector 𝕜 p 0 ⟨0, by decide⟩ =
    Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := p.val)
    (hs := H.measurable 0 ⟨0, by decide⟩)
    (hμs := measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) (c := (1 : 𝕜)),
    Lp.coeFn_const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜), H.root_cell_ae] with x hi hc hx
  change (indicatorConstLp p.val _ _ (1 : 𝕜)) x = _
  rw [hi, hc, indicator_of_mem hx]
  rfl

variable (hp : p.val ≠ ∞)

theorem root_average (f : IntervalLp 𝕜 p) :
    lpHaarPartitionAverage hp (H.cell 0 ⟨0, by decide⟩) f = lpHaarIntegral f := by
  rw [H.average_apply 𝕜 p hp, Measure.restrict_eq_self_of_ae_mem H.root_cell_ae]
  simp [intervalLpDyadicRadius, lpHaarIntegral_apply]

theorem backward_root (f : IntervalLp 𝕜 p) : H.backward 𝕜 p hp 0 f =
    lpHaarIntegral f • Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜) := by
  rw [H.backward_eq_sum_average 𝕜 p hp 0 f]
  change (∑ k : Fin 1, lpHaarPartitionAverage hp (H.cell 0 k) f •
    lpHaarCellVector 𝕜 p 0 k) = _
  rw [Fin.sum_univ_one]
  change lpHaarPartitionAverage hp (H.cell 0 ⟨0, by decide⟩) f •
    lpHaarCellVector 𝕜 p 0 0 = _
  rw [H.root_average 𝕜 p hp f, lpHaarCellVector_root_eq_const]

theorem backward_integral (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarIntegral (H.backward 𝕜 p hp n f) = lpHaarIntegral f := by
  induction n with
  | zero => rw [H.backward_root 𝕜 p hp f, map_smul, lpHaarIntegral_const, smul_eq_mul, mul_one]
  | succ n ih =>
      rw [H.backward_adjacent 𝕜 p hp n f, map_add, map_sum, ih]
      have hz : (∑ k : Fin (2 ^ n), lpHaarIntegral
          (H.nodeReader 𝕜 p n k f • lpHaarDyadic 𝕜 p n k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [map_smul, lpHaarIntegral_apply, lpHaarDyadic_integral_zero 𝕜 p n k k.isLt, smul_zero]
      rw [hz, add_zero]

theorem reading_integral (A : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hA : ∀ f, Tendsto (fun n => H.backward 𝕜 p hp n f) atTop (𝓝 (A f)))
    (f : IntervalLp 𝕜 p) : lpHaarIntegral (A f) = lpHaarIntegral f := by
  have h := (lpHaarIntegral.continuous.tendsto (A f)).comp (hA f)
  have hc : Tendsto (fun n => lpHaarIntegral (H.backward 𝕜 p hp n f)) atTop
      (𝓝 (lpHaarIntegral f)) := by
    simpa only [H.backward_integral 𝕜 p hp] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => lpHaarIntegral f) atTop (𝓝 (lpHaarIntegral f)))
  exact tendsto_nhds_unique h hc

theorem embedding_const (B : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hB : ∀ f, Tendsto (fun n => H.forward 𝕜 p hp n f) atTop (𝓝 (B f))) :
    B (lpHaarRawVector 𝕜 p none) = lpHaarRawVector 𝕜 p none := by
  let v := lpHaarRawVector 𝕜 p none
  have hroot : lpHaarDyadicMean 𝕜 p hp 0 v = v := by
    rw [lpHaarDyadicMean_root]
    simp only [v, lpHaarRawCoordinate, lpHaarRawVector, lpHaarIntegral_const, one_smul]
  have hf : H.forward 𝕜 p hp 0 v = v := by
    change H.forward 𝕜 p hp 0 (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)) = _
    rw [← lpHaarCellVector_root_eq_const]
    exact (H.forward_cell 𝕜 p hp 0 ⟨0, by decide⟩).trans (H.root_vector_const 𝕜 p)
  have hs := H.forward_stable_of_mean_fix 𝕜 p hp 0 v hroot
  have hc : Tendsto (fun n => H.forward 𝕜 p hp n v) atTop (𝓝 v) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun n => ((hs n (Nat.zero_le n)).trans hf).symm)
  exact tendsto_nhds_unique (hB v) hc

theorem nodeVector_integral (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarIntegral (H.nodeVector 𝕜 p n k) = 0 := by
  rw [lpHaarIntegral_apply]
  apply lpHaarVector_integral_zero
  rw [H.measure, H.measure]

theorem embedding_integral (B : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hB : ∀ f, Tendsto (fun n => H.forward 𝕜 p hp n f) atTop (𝓝 (B f)))
    (f : IntervalLp 𝕜 p) : lpHaarIntegral (B f) = lpHaarIntegral f := by
  have he : (lpHaarIntegral (𝕜 := 𝕜) (p := p.val)
      (μ := volume.restrict (Icc (0 : ℝ) 1))).comp B = lpHaarIntegral := by
    apply (intervalLpHaarBasis 𝕜 p hp).operator_ext
    intro j
    change lpHaarIntegral (B (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv j))) =
      lpHaarIntegral (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv j))
    simp only [lpHaarNormalizedVector, map_smul]
    congr 1
    cases he : lpHaarIndexEquiv j with
    | none => rw [H.embedding_const 𝕜 p hp B hB]
    | some i =>
        rcases i with ⟨n, k⟩
        simp only [lpHaarRawVector]
        rw [H.embedding_haar 𝕜 p hp B hB n k, H.nodeVector_integral 𝕜 p n k,
          lpHaarIntegral_apply, lpHaarDyadic_integral_zero 𝕜 p n k k.isLt]
  exact congrArg (fun T : IntervalLp 𝕜 p →L[𝕜] 𝕜 => T f) he

end LpHaarPartitionTree

def intervalLpMeanZeroRestrict (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hT : ∀ f, lpHaarIntegral f = 0 → lpHaarIntegral (T f) = 0) :
    IntervalLpMeanZero 𝕜 p →L[𝕜] IntervalLpMeanZero 𝕜 p :=
  (T.comp (intervalLpMeanZeroSubmodule 𝕜 p).subtypeL).codRestrict
    (intervalLpMeanZeroSubmodule 𝕜 p) (fun f => hT f f.property)

theorem norm_intervalLpMeanZeroRestrict_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hT : ∀ f, lpHaarIntegral f = 0 → lpHaarIntegral (T f) = 0) :
    ‖intervalLpMeanZeroRestrict 𝕜 p T hT‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  change ‖T f.val‖ ≤ ‖T‖ * ‖f.val‖
  exact T.le_opNorm f.val

theorem LpHaarPartitionTree.exists_faithful_meanZero_retraction
    (H : LpHaarPartitionTree) (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
    (hH : H.FaithfulSplits) :
    ∃ A B : IntervalLpMeanZero 𝕜 p →L[𝕜] IntervalLpMeanZero 𝕜 p,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ A.comp B = ContinuousLinearMap.id 𝕜 (IntervalLpMeanZero 𝕜 p) ∧
        ∀ f, ‖B f‖ = ‖f‖ := by
  obtain ⟨A, B, hA, hB, hAB, hiso, hAlim, hBlim⟩ := H.exists_faithful_retraction 𝕜 p hp hH
  have hAz (f : IntervalLp 𝕜 p) (hf : lpHaarIntegral f = 0) : lpHaarIntegral (A f) = 0 :=
    (H.reading_integral 𝕜 p hp A hAlim f).trans hf
  have hBz (f : IntervalLp 𝕜 p) (hf : lpHaarIntegral f = 0) : lpHaarIntegral (B f) = 0 :=
    (H.embedding_integral 𝕜 p hp B hBlim f).trans hf
  let Ar := intervalLpMeanZeroRestrict 𝕜 p A hAz
  let Br := intervalLpMeanZeroRestrict 𝕜 p B hBz
  refine ⟨Ar, Br, (norm_intervalLpMeanZeroRestrict_le 𝕜 p A hAz).trans hA,
    (norm_intervalLpMeanZeroRestrict_le 𝕜 p B hBz).trans hB, ?_, fun f => hiso f.val⟩
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change A (B f.val) = f.val
  exact congrArg (fun T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p => T f.val) hAB

end ThesisCommon
