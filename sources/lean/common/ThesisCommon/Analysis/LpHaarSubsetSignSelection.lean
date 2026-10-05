import ThesisCommon.Analysis.LpHaarSignSelection
import ThesisCommon.Analysis.LpHaarSignedBlocks

/-! Signed blocks supported on prescribed dyadic parents can meet any
finite family of small functional constraints at sufficiently late levels.
The subsets may depend on the level, as in the faithful-block recursion. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
include hp

theorem lpHaarDyadic_subset_variance_le (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (φ : IntervalLp 𝕜 p →L[𝕜] 𝕜) :
    (∑ k : Fin (2 ^ n), ‖φ (if k ∈ S then lpHaarDyadic 𝕜 p n k else 0)‖ ^ 2) ≤
      ‖φ‖ ^ 2 * intervalLpDyadicRadius n ^ (1 / p.val.toReal) := by
  apply le_trans _ (lpHaarDyadic_functional_variance_le 𝕜 p hp φ n)
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ S
  · simp [hk]
  · simp [hk, sq_nonneg]

theorem lpHaarSignedBlock_subset_small {m : ℕ}
    (φ : Fin m → IntervalLp 𝕜 p →L[𝕜] 𝕜)
    (S : ∀ n, Finset (Fin (2 ^ n))) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n ≥ N, ∃ θ : Fin (2 ^ n) → Bool,
      ∀ r, ‖φ r (lpHaarSignedBlock 𝕜 p n (S n) θ)‖ < ε := by
  have ht (r : Fin m) : Tendsto
      (fun n => ∑ k : Fin (2 ^ n),
        ‖φ r (if k ∈ S n then lpHaarDyadic 𝕜 p n k else 0)‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => Finset.sum_nonneg fun k _ => sq_nonneg _)
      (fun n => lpHaarDyadic_subset_variance_le 𝕜 p hp n (S n) (φ r))
    simpa using tendsto_const_nhds.mul (lpHaarDyadic_norm_radius_tendsto_zero p hp)
  have htotal : Tendsto
      (fun n => ∑ r : Fin m, ∑ k : Fin (2 ^ n),
        ‖φ r (if k ∈ S n then lpHaarDyadic 𝕜 p n k else 0)‖ ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun r _ => ht r)
  have hg := (tendsto_order.mp htotal).2 (ε ^ 2) (sq_pos_of_pos hε)
  obtain ⟨n, hn, hsmall⟩ := ((eventually_ge_atTop N).and hg).exists
  obtain ⟨θ, hθ⟩ := haar_sign_simultaneous_small
    (fun r k => φ r (if k ∈ S n then lpHaarDyadic 𝕜 p n k else 0)) hε hsmall
  refine ⟨n, hn, θ, fun r => ?_⟩
  have heq : φ r (lpHaarSignedBlock 𝕜 p n (S n) θ) =
      ∑ k : Fin (2 ^ n), signedValue (θ k)
        (φ r (if k ∈ S n then lpHaarDyadic 𝕜 p n k else 0)) := by
    rw [lpHaarSignedBlock, map_sum]
    have hterm (k : Fin (2 ^ n)) :
        signedValue (θ k) (φ r (if k ∈ S n then lpHaarDyadic 𝕜 p n k else 0)) =
        if k ∈ S n then φ r (signedValue (θ k) (lpHaarDyadic 𝕜 p n k)) else 0 := by
      by_cases hk : k ∈ S n <;> cases θ k <;> simp [signedValue, hk]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    have hfilter : Finset.univ.filter (fun k => k ∈ S n) = S n := by ext k; simp
    rw [hfilter]
  rw [heq]
  exact hθ r

end ThesisCommon
