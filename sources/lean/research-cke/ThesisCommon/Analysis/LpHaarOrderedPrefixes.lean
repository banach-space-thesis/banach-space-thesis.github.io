import ThesisCommon.Analysis.LpHaarPartialLevels
import Mathlib.Data.Nat.Log

/-! Uniformly bounded Haar prefixes and their convergence in the natural
level order, including partial final levels. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace ThesisCommon

theorem norm_lpHaarLevelProjection_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) : ‖lpHaarLevelProjection 𝕜 p n‖ ≤ 2 := by
  rw [← lpHaarDyadicMean_difference_operator 𝕜 p hp n]
  exact (norm_sub_le _ _).trans (by
    linarith [lpHaarDyadicMean_norm_le 𝕜 p hp (n + 1), lpHaarDyadicMean_norm_le 𝕜 p hp n])

theorem norm_lpHaarPartialLevel_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    ‖lpHaarPartialLevel 𝕜 p n S‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  exact (lpHaarPartialLevel_norm_le 𝕜 p n S f).trans
    (((lpHaarLevelProjection 𝕜 p n).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (norm_lpHaarLevelProjection_le 𝕜 p hp n) (norm_nonneg f)))

def lpHaarPrefix (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  lpHaarDyadicMean 𝕜 p hp n + lpHaarPartialLevel 𝕜 p n S

theorem norm_lpHaarPrefix_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    ‖lpHaarPrefix 𝕜 p hp n S‖ ≤ 3 := by
  exact (norm_add_le _ _).trans (by
    linarith [lpHaarDyadicMean_norm_le 𝕜 p hp n, norm_lpHaarPartialLevel_le 𝕜 p hp n S])

theorem lpHaarPrefix_tendsto (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (L : ℕ → ℕ) (hL : Tendsto L atTop atTop)
    (S : ∀ N, Finset (Fin (2 ^ L N))) (f : IntervalLp 𝕜 p) :
    Tendsto (fun N => lpHaarPrefix 𝕜 p hp (L N) (S N) f) atTop (𝓝 f) := by
  have hsmall : Tendsto (fun N => lpHaarPartialLevel 𝕜 p (L N) (S N) f) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun N => norm_nonneg _)
      (fun N => lpHaarPartialLevel_norm_le 𝕜 p (L N) (S N) f)
    simpa only [norm_zero] using ((lpHaarLevelProjection_tendsto_zero 𝕜 p hp f).comp hL).norm
  have h := ((lpHaarDyadicMean_tendsto 𝕜 p hp f).comp hL).add hsmall
  simpa only [Function.comp_apply, add_zero] using h

theorem lpHaarLevelIndex_tendsto : Tendsto (fun N : ℕ => Nat.log2 (N + 1)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop (2 ^ n)] with N hN
  exact (Nat.le_log2 (Nat.succ_ne_zero N)).mpr (hN.trans (Nat.le_succ N))

/-- The prefix through position `N`, with constant at position zero and
`h_(n,k)` at position `2^n+k`. -/
def lpHaarNaturalPrefix (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
    (N : ℕ) : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  lpHaarPrefix 𝕜 p hp (Nat.log2 (N + 1))
    (Finset.univ.filter (fun k : Fin (2 ^ Nat.log2 (N + 1)) => 2 ^ Nat.log2 (N + 1) + k.val < N + 1))

theorem norm_lpHaarNaturalPrefix_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (N : ℕ) : ‖lpHaarNaturalPrefix 𝕜 p hp N‖ ≤ 3 :=
  norm_lpHaarPrefix_le 𝕜 p hp _ _

theorem lpHaarNaturalPrefix_tendsto (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (f : IntervalLp 𝕜 p) :
    Tendsto (fun N => lpHaarNaturalPrefix 𝕜 p hp N f) atTop (𝓝 f) :=
  lpHaarPrefix_tendsto 𝕜 p hp _ lpHaarLevelIndex_tendsto _ f

end ThesisCommon
