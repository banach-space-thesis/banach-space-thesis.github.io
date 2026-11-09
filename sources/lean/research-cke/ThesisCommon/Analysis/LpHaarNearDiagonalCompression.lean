import ThesisCommon.Analysis.LpHaarNormalizedCompression
import ThesisCommon.Analysis.SchauderGeometricPerturbation

/-! The first Alspach--Enflo--Odell reduction on actual interval Lp.
Operators whose range is mean-zero and which kill constants admit a
contractive block compression arbitrarily close to an actual bounded
Haar diagonal operator. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem lpHaar_raw_action_of_normalized_diagonal
    (S D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hD : ∀ j, D ((intervalLpHaarBasis 𝕜 p hp).vector j) =
      (intervalLpHaarBasis 𝕜 p hp).coord j (S ((intervalLpHaarBasis 𝕜 p hp).vector j)) •
        (intervalLpHaarBasis 𝕜 p hp).vector j)
    (n : ℕ) (k : Fin (2 ^ n)) :
    D (lpHaarDyadic 𝕜 p n k) =
      lpHaarDyadicCoefficient 𝕜 p n k (S (lpHaarDyadic 𝕜 p n k)) • lpHaarDyadic 𝕜 p n k := by
  let i : Option LpHaarTreeIndex := some ⟨n, k⟩
  have he : lpHaarIndexEquiv (lpHaarEncode i) = i := lpHaarDecode_encode i
  have h := hD (lpHaarEncode i)
  change D (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv (lpHaarEncode i))) =
    lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv (lpHaarEncode i))
      (S (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv (lpHaarEncode i)))) •
        lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv (lpHaarEncode i)) at h
  rw [he, lpHaarRawCoordinate_diagonal_normalized 𝕜 p hp S i,
    lpHaarNormalizedVector, map_smul] at h
  have hn : (‖lpHaarRawVector 𝕜 p i‖ : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (lpHaarRawVector_norm_pos 𝕜 p hp i).ne'
  have hh := congrArg (fun x : IntervalLp 𝕜 p => (‖lpHaarRawVector 𝕜 p i‖ : 𝕜) • x) h
  have hcancel (z : 𝕜) : (‖lpHaarRawVector 𝕜 p i‖ : 𝕜) *
      (z * (‖lpHaarRawVector 𝕜 p i‖ : 𝕜)⁻¹) = z := by
    rw [mul_comm z, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  simpa only [lpHaarNormalizedVector, smul_smul, mul_inv_cancel₀ hn,
    hcancel, one_smul] using hh

include hp in
theorem lpHaar_near_diagonal_compression
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (hTmean : ∀ f, lpHaarIntegral (T f) = 0)
    (hTconst : T (lpHaarRawVector 𝕜 p none) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A B D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ A.comp B = ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) ∧
      (∀ f, lpHaarIntegral (A f) = lpHaarIntegral f) ∧
      (∀ f, lpHaarIntegral (B f) = lpHaarIntegral f) ∧
      ‖((A.comp T).comp B) - D‖ ≤ ε / 4 ∧
      ∀ n (k : Fin (2 ^ n)), D (lpHaarDyadic 𝕜 p n k) =
        lpHaarDyadicCoefficient 𝕜 p n k (((A.comp T).comp B) (lpHaarDyadic 𝕜 p n k)) •
          lpHaarDyadic 𝕜 p n k := by
  let c := ε / 24
  have hc : 0 < c := div_pos hε (by norm_num)
  obtain ⟨F, hF⟩ := lpHaar_infinite_normalized_selection 𝕜 p hp T
    (fun j => c * (1 / 2 : ℝ) ^ (2 * j + 4)) (fun j => mul_pos hc (pow_pos (by norm_num) _))
  obtain ⟨A, B, hA, hB, hAB, hiso, hAlim, hBlim⟩ :=
    F.toPartitionTree.exists_faithful_retraction 𝕜 p hp F.faithful
  let S := (A.comp T).comp B
  have hSmean (f : IntervalLp 𝕜 p) : lpHaarIntegral (S f) = 0 :=
    (F.toPartitionTree.reading_integral 𝕜 p hp A hAlim _).trans (hTmean _)
  have hSconst : S (lpHaarRawVector 𝕜 p none) = 0 := by
    change A (T (B (lpHaarRawVector 𝕜 p none))) = 0
    rw [F.toPartitionTree.embedding_const 𝕜 p hp B hBlim, hTconst, map_zero]
  let b := intervalLpHaarBasis 𝕜 p hp
  have hentries (i j : ℕ) (hij : i ≠ j) :
      ‖b.coord i (S (b.vector j))‖ ≤ c * (1 / 2 : ℝ) ^ (i + j + 2) := by
    change ‖lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv i)
      (S (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv j)))‖ ≤ _
    cases hi : lpHaarIndexEquiv i with
    | none =>
        simp only [lpHaarNormalizedCoordinate, ContinuousLinearMap.smul_apply,
          lpHaarRawCoordinate, hSmean, smul_zero, norm_zero]
        positivity
    | some u =>
        rcases u with ⟨n, k⟩
        cases hj : lpHaarIndexEquiv j with
        | none =>
            rw [lpHaarNormalizedVector, map_smul, hSconst, smul_zero, map_zero, norm_zero]
            positivity
        | some v =>
            rcases v with ⟨m, l⟩
            rw [F.normalized_compression_coefficient 𝕜 p hp A B T hAlim hBlim hiso]
            have hi' := lpHaarHeapIndex_decode hi
            have hj' := lpHaarHeapIndex_decode hj
            have hne : lpHaarHeapIndex n k ≠ lpHaarHeapIndex m l := by omega
            rcases lt_or_gt_of_ne hne with h | h
            · have hb := (hF (lpHaarHeapIndex m l) ⟨lpHaarHeapIndex n k, h⟩).1
              apply hb.le.trans
              apply mul_le_mul_of_nonneg_left _ hc.le
              exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            · have hb := (hF (lpHaarHeapIndex n k) ⟨lpHaarHeapIndex m l, h⟩).2
              apply hb.le.trans
              apply mul_le_mul_of_nonneg_left _ hc.le
              exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  obtain ⟨D, herror, hdiag⟩ := b.exists_diagonal_of_geometric_entries
    (intervalLpHaarBasis_coord_norm_le 𝕜 p hp) hc.le S hentries
  refine ⟨A, B, D, hA, hB, hAB,
    F.toPartitionTree.reading_integral 𝕜 p hp A hAlim,
    F.toPartitionTree.embedding_integral 𝕜 p hp B hBlim, ?_, ?_⟩
  · have he : 6 * c = ε / 4 := by dsimp only [c]; ring
    exact herror.trans_eq he
  · exact lpHaar_raw_action_of_normalized_diagonal 𝕜 p hp S D hdiag

end ThesisCommon
