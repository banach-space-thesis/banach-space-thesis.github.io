import ThesisCommon.Analysis.LpHaarAncestors
import ThesisCommon.Analysis.LpHaarSchauderBasis
import ThesisCommon.Analysis.SchauderOperators

/-! Summable changes along Haar-tree edges control the operator norm.
The proof is a norm-convergent series of actual subtree projections.
It applies over real and complex scalars and does not use an
unconditional Haar basis. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def lpHaarSubtreeTerm (a : LpHaarTreeIndex → 𝕜) (i : LpHaarTreeIndex) :
    IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p := a i • lpHaarSubtreeProjection 𝕜 p hp i.1 i.2

theorem norm_lpHaarSubtreeTerm_le (a : LpHaarTreeIndex → 𝕜) (i : LpHaarTreeIndex) :
    ‖lpHaarSubtreeTerm 𝕜 p hp a i‖ ≤ 2 * ‖a i‖ := by
  rw [lpHaarSubtreeTerm, norm_smul]
  calc
    _ ≤ ‖a i‖ * 2 := mul_le_mul_of_nonneg_left
      (norm_lpHaarSubtreeProjection_le 𝕜 p hp i.1 i.2) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem summable_lpHaarSubtreeTerms (a : LpHaarTreeIndex → 𝕜)
    (ha : Summable (fun i => ‖a i‖)) : Summable (lpHaarSubtreeTerm 𝕜 p hp a) :=
  (ha.mul_left 2).of_norm_bounded (norm_lpHaarSubtreeTerm_le 𝕜 p hp a)

def lpHaarSubtreeSeries (a : LpHaarTreeIndex → 𝕜) :
    IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p := ∑' i, lpHaarSubtreeTerm 𝕜 p hp a i

theorem norm_lpHaarSubtreeSeries_le (a : LpHaarTreeIndex → 𝕜)
    (ha : Summable (fun i => ‖a i‖)) :
    ‖lpHaarSubtreeSeries 𝕜 p hp a‖ ≤ 2 * ∑' i, ‖a i‖ := by
  have hn : Summable (fun i => ‖lpHaarSubtreeTerm 𝕜 p hp a i‖) :=
    (ha.mul_left 2).of_nonneg_of_le (fun i => norm_nonneg _)
      (norm_lpHaarSubtreeTerm_le 𝕜 p hp a)
  calc
    _ ≤ ∑' i, ‖lpHaarSubtreeTerm 𝕜 p hp a i‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i, 2 * ‖a i‖ := hn.tsum_le_tsum
      (norm_lpHaarSubtreeTerm_le 𝕜 p hp a) (ha.mul_left 2)
    _ = _ := tsum_mul_left

theorem lpHaarSubtreeSeries_haar (a : LpHaarTreeIndex → 𝕜)
    (ha : Summable (fun i => ‖a i‖)) (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarSubtreeSeries 𝕜 p hp a (lpHaarDyadic 𝕜 p n k) =
      (∑ i ∈ lpHaarAncestors n k, a i) • lpHaarDyadic 𝕜 p n k := by
  let ev := ContinuousLinearMap.apply 𝕜 (IntervalLp 𝕜 p) (lpHaarDyadic 𝕜 p n k)
  change ev (∑' i, lpHaarSubtreeTerm 𝕜 p hp a i) = _
  rw [ev.map_tsum (summable_lpHaarSubtreeTerms 𝕜 p hp a ha)]
  have he (i : LpHaarTreeIndex) : ev (lpHaarSubtreeTerm 𝕜 p hp a i) =
      if i ∈ lpHaarAncestors n k then a i • lpHaarDyadic 𝕜 p n k else 0 := by
    change a i • lpHaarSubtreeProjection 𝕜 p hp i.1 i.2 (lpHaarDyadic 𝕜 p n k) = _
    rw [lpHaarSubtreeProjection_haar]
    split_ifs <;> simp
  simp_rw [he]
  rw [tsum_eq_sum (s := lpHaarAncestors n k) (fun i hi => by simp [hi])]
  have hs : (∑ i ∈ lpHaarAncestors n k, a i • lpHaarDyadic 𝕜 p n k) =
      (∑ i ∈ lpHaarAncestors n k, a i) • lpHaarDyadic 𝕜 p n k := Finset.sum_smul.symm
  simpa only [Finset.sum_ite_mem, Finset.inter_self] using hs

variable {𝕜}

def lpHaarEdgeDifference (d : LpHaarTreeIndex → 𝕜) (c : 𝕜) : LpHaarTreeIndex → 𝕜
  | ⟨0, k⟩ => d ⟨0, k⟩ - c
  | ⟨n + 1, k⟩ => d ⟨n + 1, k⟩ - d ⟨n, lpHaarParentIndex n k⟩

theorem lpHaarEdgeDifference_path (d : LpHaarTreeIndex → 𝕜) (c : 𝕜)
    (n : ℕ) (k : Fin (2 ^ n)) :
    (∑ i ∈ lpHaarAncestors n k, lpHaarEdgeDifference d c i) = d ⟨n, k⟩ - c := by
  induction n with
  | zero => simp [lpHaarAncestors, lpHaarEdgeDifference]
  | succ n ih =>
      have hnew : (⟨n + 1, k⟩ : LpHaarTreeIndex) ∉
          lpHaarAncestors n (lpHaarParentIndex n k) := by
        intro h
        have := lpHaarAncestors_level_le n (lpHaarParentIndex n k) ⟨n + 1, k⟩ h
        change n + 1 ≤ n at this
        omega
      rw [lpHaarAncestors, Finset.sum_insert hnew, lpHaarEdgeDifference, ih]
      ring

variable (𝕜)
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

theorem lpHaarSubtreeProjection_const (n k : ℕ) :
    lpHaarSubtreeProjection 𝕜 p hp n k
      (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)) = 0 := by
  let v := lpHaarRawVector 𝕜 p none
  have hroot : lpHaarDyadicMean 𝕜 p hp 0 v = v := by
    rw [lpHaarDyadicMean_root]
    simp only [v, lpHaarRawCoordinate, lpHaarRawVector, lpHaarIntegral_const, one_smul]
  have hn : lpHaarDyadicMean 𝕜 p hp n v = v := by
    calc
      _ = lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadicMean 𝕜 p hp 0 v) := congrArg _ hroot.symm
      _ = _ := (lpHaarDyadicMean_nested_forward 𝕜 p hp 0 n (Nat.zero_le n) v).trans hroot
  change lpHaarSubtreeProjection 𝕜 p hp n k v = 0
  rw [lpHaarSubtreeProjection_apply, hn, sub_self, map_zero]

theorem lpHaarSubtreeSeries_const (a : LpHaarTreeIndex → 𝕜)
    (ha : Summable (fun i => ‖a i‖)) :
    lpHaarSubtreeSeries 𝕜 p hp a
      (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)) = 0 := by
  let v := Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)
  let ev := ContinuousLinearMap.apply 𝕜 (IntervalLp 𝕜 p) v
  change ev (∑' i, lpHaarSubtreeTerm 𝕜 p hp a i) = 0
  rw [ev.map_tsum (summable_lpHaarSubtreeTerms 𝕜 p hp a ha)]
  have hz (i : LpHaarTreeIndex) : ev (lpHaarSubtreeTerm 𝕜 p hp a i) = 0 := by
    change a i • lpHaarSubtreeProjection 𝕜 p hp i.1 i.2 v = 0
    rw [lpHaarSubtreeProjection_const, smul_zero]
  simp_rw [hz]
  exact tsum_zero

def lpHaarMeanRootCorrection (D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (c : 𝕜) :
    IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  (lpHaarIntegral (𝕜 := 𝕜) (p := p.val) (μ := volume.restrict (Icc (0 : ℝ) 1))).smulRight
    (D (lpHaarRawVector 𝕜 p none) - c • lpHaarRawVector 𝕜 p none)

include hp in
theorem lpHaar_diagonal_edge_norm_le (D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (d : LpHaarTreeIndex → 𝕜) (c : 𝕜)
    (hD : ∀ n (k : Fin (2 ^ n)), D (lpHaarDyadic 𝕜 p n k) = d ⟨n, k⟩ • lpHaarDyadic 𝕜 p n k)
    (ha : Summable (fun i => ‖lpHaarEdgeDifference d c i‖)) :
    ‖D - c • ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) - lpHaarMeanRootCorrection 𝕜 p D c‖ ≤
      2 * ∑' i, ‖lpHaarEdgeDifference d c i‖ := by
  let E := D - c • ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) - lpHaarMeanRootCorrection 𝕜 p D c
  have he : E = lpHaarSubtreeSeries 𝕜 p hp (lpHaarEdgeDifference d c) := by
    apply (intervalLpHaarBasis 𝕜 p hp).operator_ext
    intro j
    change E (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv j)) =
      lpHaarSubtreeSeries 𝕜 p hp (lpHaarEdgeDifference d c)
        (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv j))
    rw [lpHaarNormalizedVector, map_smul, map_smul]
    congr 1
    cases he : lpHaarIndexEquiv j with
    | none =>
        simp only [lpHaarRawVector]
        rw [lpHaarSubtreeSeries_const 𝕜 p hp _ ha]
        simp only [E, lpHaarMeanRootCorrection, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.smulRight_apply, lpHaarRawVector, lpHaarIntegral_const, one_smul]
        abel
    | some i =>
        rcases i with ⟨n, k⟩
        simp only [lpHaarRawVector]
        rw [lpHaarSubtreeSeries_haar 𝕜 p hp _ ha n k, lpHaarEdgeDifference_path]
        simp only [E, lpHaarMeanRootCorrection, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.smulRight_apply, lpHaarIntegral_apply,
          lpHaarDyadic_integral_zero 𝕜 p n k k.isLt, zero_smul, sub_zero, hD n k]
        module
  change ‖E‖ ≤ _
  rw [he]
  exact norm_lpHaarSubtreeSeries_le 𝕜 p hp _ ha

include hp in
theorem lpHaar_diagonal_edge_meanZero_bound (D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (d : LpHaarTreeIndex → 𝕜) (c : 𝕜)
    (hD : ∀ n (k : Fin (2 ^ n)), D (lpHaarDyadic 𝕜 p n k) = d ⟨n, k⟩ • lpHaarDyadic 𝕜 p n k)
    (ha : Summable (fun i => ‖lpHaarEdgeDifference d c i‖))
    (f : IntervalLp 𝕜 p) (hf : lpHaarIntegral f = 0) :
    ‖D f - c • f‖ ≤ (2 * ∑' i, ‖lpHaarEdgeDifference d c i‖) * ‖f‖ := by
  let E := D - c • ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) - lpHaarMeanRootCorrection 𝕜 p D c
  have he : E f = D f - c • f := by
    simp only [E, lpHaarMeanRootCorrection, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, hf, zero_smul, sub_zero]
  rw [← he]
  exact E.le_of_opNorm_le (lpHaar_diagonal_edge_norm_le 𝕜 p hp D d c hD ha) f

end ThesisCommon
