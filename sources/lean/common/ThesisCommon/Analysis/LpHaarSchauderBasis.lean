import ThesisCommon.Analysis.LpHaarRootMean
import ThesisCommon.Analysis.LpHaarOrderedPrefixes
import ThesisCommon.Analysis.LpHaarEnumerationSums
import ThesisCommon.Analysis.SchauderBasis

/-! A normalized Haar Schauder basis of the genuine interval Lp space for
every finite exponent at least one, over either real or complex scalars. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace ThesisCommon

variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem lpHaarRaw_prefix_eq (N : ℕ) (f : IntervalLp 𝕜 p) :
    (∑ i ∈ Finset.range (N + 1),
      lpHaarRawCoordinate 𝕜 p (lpHaarDecode i) f • lpHaarRawVector 𝕜 p (lpHaarDecode i)) =
      lpHaarNaturalPrefix 𝕜 p hp N f := by
  rw [lpHaar_sum_decoded_prefix_fin
    (fun i => lpHaarRawCoordinate 𝕜 p i f • lpHaarRawVector 𝕜 p i) (Nat.succ_ne_zero N)]
  have hroot := lpHaarDyadicMean_root 𝕜 p hp f
  simp only [lpHaarRawCoordinate, lpHaarRawVector] at hroot ⊢
  rw [← hroot]
  simp_rw [← lpHaarLevelProjection_apply]
  rw [← lpHaarDyadicMean_eq_partialSum 𝕜 p hp]
  rw [lpHaarNaturalPrefix, lpHaarPrefix, ContinuousLinearMap.add_apply,
    lpHaarPartialLevel_apply, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hle := lpHaar_pow_log2_le (Nat.succ_ne_zero N)
  have hiff : k.val < N + 1 - 2 ^ (N + 1).log2 ↔
      2 ^ (N + 1).log2 + k.val < N + 1 := by omega
  simp only [hiff]

include hp in
theorem lpHaarNormalized_expansion (f : IntervalLp 𝕜 p) :
    Tendsto (fun N => ∑ i ∈ Finset.range N,
      lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv i) f •
        lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv i)) atTop (𝓝 f) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simp_rw [lpHaarNormalized_term 𝕜 p hp]
  change Tendsto (fun N => ∑ i ∈ Finset.range (N + 1),
    lpHaarRawCoordinate 𝕜 p (lpHaarDecode i) f • lpHaarRawVector 𝕜 p (lpHaarDecode i))
      atTop (𝓝 f)
  simp_rw [lpHaarRaw_prefix_eq 𝕜 p hp]
  exact lpHaarNaturalPrefix_tendsto 𝕜 p hp f

/-- The genuine normalized Haar basis, with constant vector at position zero
and the level `n`, cell `k` Haar vector at position `2^n+k`. -/
def intervalLpHaarBasis : NormalizedSchauderBasis 𝕜 (IntervalLp 𝕜 p) where
  vector i := lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv i)
  coord i := lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv i)
  biorthogonal i j := by
    simpa only [Equiv.apply_eq_iff_eq] using
      lpHaarNormalized_biorthogonal 𝕜 p hp (lpHaarIndexEquiv i) (lpHaarIndexEquiv j)
  norm_vector i := lpHaarNormalizedVector_norm 𝕜 p hp (lpHaarIndexEquiv i)
  expansion := lpHaarNormalized_expansion 𝕜 p hp

theorem intervalLpHaarBasis_prefix_norm_le (N : ℕ) (f : IntervalLp 𝕜 p) :
    ‖∑ i ∈ Finset.range N,
      (intervalLpHaarBasis 𝕜 p hp).coord i f • (intervalLpHaarBasis 𝕜 p hp).vector i‖ ≤
      3 * ‖f‖ := by
  cases N with
  | zero => simp
  | succ N =>
      change ‖∑ i ∈ Finset.range (N + 1),
        lpHaarNormalizedCoordinate 𝕜 p (lpHaarIndexEquiv i) f •
          lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv i)‖ ≤ _
      simp_rw [lpHaarNormalized_term 𝕜 p hp]
      change ‖∑ i ∈ Finset.range (N + 1),
        lpHaarRawCoordinate 𝕜 p (lpHaarDecode i) f • lpHaarRawVector 𝕜 p (lpHaarDecode i)‖ ≤ _
      rw [lpHaarRaw_prefix_eq 𝕜 p hp]
      exact ((lpHaarNaturalPrefix 𝕜 p hp N).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (norm_lpHaarNaturalPrefix_le 𝕜 p hp N) (norm_nonneg f))

end ThesisCommon
