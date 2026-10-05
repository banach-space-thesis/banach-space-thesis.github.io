import ThesisCommon.Analysis.SchauderSumBasis
import ThesisCommon.Analysis.SchauderSumInsertion

/-! Weak nullity of the actual product basis. Large entries in infinitely
many rows would give a bounded insertion contradicting outer weak nullity.
There are then only finitely many remaining rows; inner weak nullity controls
each of them. This expands the row/fibre argument in the CKL proof.
-/
noncomputable section
open Filter Topology
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}
variable (c : NormalizedSchauderBasis 𝕜 Y)

/-- Outer weak nullity controls all entries of sufficiently late rows,
uniformly over the inner basis index. -/
theorem product_uniform_row_bound
    (hwb : ∀ ψ : X →L[𝕜] 𝕜, Tendsto (fun i => ψ (b.vector i)) atTop (𝓝 0))
    (φ : SchauderSum b hb Y →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ i, N ≤ i → ∀ j, ‖φ (productVector c (i, j))‖ < ε := by
  classical
  have hj (i : ℕ) : ∃ j : ℕ,
      (∃ k, ε ≤ ‖φ (productVector c (i, k))‖) →
        ε ≤ ‖φ (productVector c (i, j))‖ := by
    by_cases hi : ∃ k, ε ≤ ‖φ (productVector c (i, k))‖
    · obtain ⟨j, hj⟩ := hi; exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose j hj using hj
  obtain ⟨B, _, hB⟩ := exists_vector_insertion (b := b) (hb := hb)
    (fun i => c.vector (j i)) (fun i => (c.norm_vector _).le)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hwb (φ.comp B)) ε hε
  refine ⟨N, ?_⟩
  intro i hi k
  have hn : ‖φ (productVector c (i, j i))‖ < ε := by
    simpa only [dist_zero_right, ContinuousLinearMap.comp_apply, hB, productVector] using hN i hi
  by_contra hk
  exact (not_le_of_gt hn) (hj i ⟨k, le_of_not_gt hk⟩)

/-- The product of two weakly null normalized bases is weakly null in
every bijective ordering, with the genuine vector-valued sum norm. -/
theorem product_weakly_null
    (hwb : ∀ ψ : X →L[𝕜] 𝕜, Tendsto (fun i => ψ (b.vector i)) atTop (𝓝 0))
    (hwc : ∀ ψ : Y →L[𝕜] 𝕜, Tendsto (fun j => ψ (c.vector j)) atTop (𝓝 0))
    (e : ℕ ≃ ℕ × ℕ) (φ : SchauderSum b hb Y →L[𝕜] 𝕜) :
    Tendsto (fun k => φ (productVector c (e k))) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  simp only [dist_zero_right]
  obtain ⟨N, hN⟩ := product_uniform_row_bound c hwb φ hε
  have hm (i : ℕ) : ∃ M, ∀ j, M ≤ j → ‖φ (productVector c (i, j))‖ < ε := by
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp
      (hwc (φ.comp (singleL (b := b) (hb := hb) (Y := Y) i))) ε hε
    exact ⟨M, fun j hj => by
      simpa only [dist_zero_right, ContinuousLinearMap.comp_apply, singleL_apply, productVector]
        using hM j hj⟩
  choose M hM using hm
  let F : Finset ℕ := (Finset.range N).biUnion (fun i =>
    (Finset.range (M i)).image (fun j => e.symm (i, j)))
  refine ⟨F.sup id + 1, ?_⟩
  intro k hk
  by_cases hi : N ≤ (e k).1
  · exact hN _ hi _
  by_cases hj : M (e k).1 ≤ (e k).2
  · exact hM _ _ hj
  have hmem : k ∈ F := by
    apply Finset.mem_biUnion.mpr
    refine ⟨(e k).1, Finset.mem_range.mpr (by omega), ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(e k).2, Finset.mem_range.mpr (by omega), e.symm_apply_apply k⟩
  have hle : k ≤ F.sup id := Finset.le_sup (f := id) hmem
  omega

end SchauderSum
end ThesisCommon
