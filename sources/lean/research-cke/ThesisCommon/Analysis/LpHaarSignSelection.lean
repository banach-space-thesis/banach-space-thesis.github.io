import ThesisCommon.Analysis.LpHaarLevelVariation

/-! Small Haar blocks for any finite family of bounded Lp functionals.
The dyadic mesh may be chosen beyond an arbitrary prescribed level. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
include hp

theorem lpHaarDyadic_norm_radius_tendsto_zero :
    Tendsto (fun n => intervalLpDyadicRadius n ^ (1 / p.val.toReal)) atTop (𝓝 0) := by
  have hpR : 0 < p.val.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one p.property)) hp
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (1 / p.val.toReal) := by positivity
  have hq1 : (1 / 2 : ℝ) ^ (1 / p.val.toReal) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  simpa only [intervalLpDyadicRadius,
    Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)] using h

theorem lpHaarDyadic_functional_variance_tendsto_zero
    (φ : IntervalLp 𝕜 p →L[𝕜] 𝕜) :
    Tendsto (fun n => ∑ k : Fin (2 ^ n), ‖φ (lpHaarDyadic 𝕜 p n k)‖ ^ 2)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => Finset.sum_nonneg fun k _ => sq_nonneg _)
    (lpHaarDyadic_functional_variance_le 𝕜 p hp φ)
  simpa using tendsto_const_nhds.mul (lpHaarDyadic_norm_radius_tendsto_zero p hp)

theorem lpHaarDyadic_signed_block_small {m : ℕ}
    (φ : Fin m → IntervalLp 𝕜 p →L[𝕜] 𝕜) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n ≥ N, ∃ θ : Fin (2 ^ n) → Bool,
      ∀ r, ‖φ r (∑ k, signedValue (θ k) (lpHaarDyadic 𝕜 p n k))‖ < ε := by
  have ht : Tendsto
      (fun n => ∑ r : Fin m, ∑ k : Fin (2 ^ n), ‖φ r (lpHaarDyadic 𝕜 p n k)‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ
      (fun r _ => lpHaarDyadic_functional_variance_tendsto_zero 𝕜 p hp (φ r))
  have hg := (tendsto_order.mp ht).2 (ε ^ 2) (sq_pos_of_pos hε)
  obtain ⟨n, hn, hsmall⟩ := ((eventually_ge_atTop N).and hg).exists
  obtain ⟨θ, hθ⟩ := haar_sign_simultaneous_small
    (fun r k => φ r (lpHaarDyadic 𝕜 p n k)) hε hsmall
  refine ⟨n, hn, θ, fun r => ?_⟩
  have hmap (k : Fin (2 ^ n)) : φ r (signedValue (θ k) (lpHaarDyadic 𝕜 p n k)) =
      signedValue (θ k) (φ r (lpHaarDyadic 𝕜 p n k)) := by
    cases θ k <;> simp [signedValue]
  simpa only [map_sum, hmap] using hθ r

end ThesisCommon
