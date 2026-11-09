import SurveyStatements.P5L1VariationFinite

/-! Passing from uniformly bounded finite branch tests to a full local
trace limit. The finite operators may vary with the terminal level. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped Topology BigOperators Classical
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem finite_branch_eigenoperators_variation_le (𝕜 : Type*) [RCLike 𝕜]
    {r : ℕ} (B : DyadicBranch r) (β : ℕ → 𝕜) (C : ℝ)
    (hfinite : ∀ N : ℕ, ∃ D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜,
      ‖D‖ ≤ C ∧ ∀ j < N + 1,
        D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
          β j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j))
    (N : ℕ) :
    (∑ j ∈ Finset.range N, ‖β (j + 1) - β j‖) ≤ 6 * C := by
  obtain ⟨D, hnorm, heigen⟩ := hfinite N
  let d : (n : ℕ) → Fin (2 ^ n) → 𝕜 := fun n _ => β (n - r)
  have hd (j : ℕ) : B.symbol 𝕜 d j = β j := by simp [DyadicBranch.symbol, d]
  have hv := B.finite_variation_le_local 𝕜 D d N (fun j hj => by
    rw [hd]
    exact heigen j hj)
  simp_rw [hd] at hv
  linarith

theorem finite_branch_eigenoperators_symbol_norm_le (𝕜 : Type*) [RCLike 𝕜]
    {r : ℕ} (B : DyadicBranch r) (β : ℕ → 𝕜) (C : ℝ)
    (hfinite : ∀ N : ℕ, ∃ D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜,
      ‖D‖ ≤ C ∧ ∀ j < N + 1,
        D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
          β j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j))
    (n : ℕ) : ‖β n‖ ≤ C := by
  obtain ⟨D, hnorm, heigen⟩ := hfinite n
  exact (single_haar_symbol_norm_le 𝕜 D (r + n) (B.index n) (β n)
    (heigen n (by omega))).trans hnorm

theorem exists_limit_of_finite_branch_eigenoperators (𝕜 : Type*) [RCLike 𝕜]
    {r : ℕ} (B : DyadicBranch r) (β : ℕ → 𝕜) (C : ℝ)
    (hfinite : ∀ N : ℕ, ∃ D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜,
      ‖D‖ ≤ C ∧ ∀ j < N + 1,
        D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
          β j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) :
    Summable (fun j => ‖β (j + 1) - β j‖) ∧
      (∑' j, ‖β (j + 1) - β j‖) ≤ 6 * C ∧
      ∃ c : 𝕜, ‖c‖ ≤ C ∧ Tendsto β atTop (𝓝 c) := by
  have hv := finite_branch_eigenoperators_variation_le 𝕜 B β C hfinite
  have hs : Summable (fun j => ‖β (j + 1) - β j‖) :=
    summable_of_sum_range_le (fun _ => norm_nonneg _) hv
  have hc : CauchySeq β := by
    apply cauchySeq_of_summable_dist
    simpa only [dist_eq_norm, norm_sub_rev] using hs
  obtain ⟨c, hlim⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨hs, hs.tsum_le_of_sum_range_le hv, c,
    le_of_tendsto hlim.norm (Eventually.of_forall
      (finite_branch_eigenoperators_symbol_norm_le 𝕜 B β C hfinite)), hlim⟩

end SurveyStatements.P5L1Variation

