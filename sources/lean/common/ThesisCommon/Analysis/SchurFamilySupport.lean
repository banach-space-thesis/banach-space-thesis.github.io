import ThesisCommon.Analysis.RCLikeEllOneSchur

/-! A family in a Schur space with sublinear finite signed-sum growth has
only countably many nonzero members. The scalar estimates are proved by
phase alignment, and the norm conclusion uses the actual Schur theorem. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 Γ E I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem finite_large_functional_of_sublinear_sums (v : Γ → E) (B : ℕ → ℝ)
    (hB : ∀ n (e : Fin n ↪ Γ) (a : Fin n → 𝕜), (∀ i, ‖a i‖ ≤ 1) →
      ‖∑ i, a i • v (e i)‖ ≤ B n)
    (hgrowth : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∃ n, M * B n < n * ε)
    (φ : E →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε) :
    {γ | ε ≤ ‖φ (v γ)‖}.Finite := by
  classical
  by_contra h
  let A : Set Γ := {γ | ε ≤ ‖φ (v γ)‖}
  have hA : A.Infinite := h
  obtain ⟨n, hn⟩ := hgrowth ‖φ‖ (norm_nonneg _) ε hε
  let e : Fin n ↪ Γ :=
    (Fin.valEmbedding.trans (hA.natEmbedding A)).trans (Function.Embedding.subtype A)
  choose a ha heq using fun i : Fin n => RCLike.exists_norm_eq_mul_self (φ (v (e i)))
  have heval : φ (∑ i, a i • v (e i)) = ((∑ i, ‖φ (v (e i))‖ : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => (heq i).symm)
  have hupper : (∑ i, ‖φ (v (e i))‖) ≤ ‖φ‖ * B n := by
    calc
      _ = ‖φ (∑ i, a i • v (e i))‖ := by
        rw [heval, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
      _ ≤ ‖φ‖ * ‖∑ i, a i • v (e i)‖ := φ.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hB n e a (fun i => (ha i).le)) (norm_nonneg _)
  have hlower : (n : ℝ) * ε ≤ ∑ i, ‖φ (v (e i))‖ := by
    calc
      _ = ∑ _i : Fin n, ε := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (hA.natEmbedding A i.val).property)
  exact (not_lt_of_ge (hlower.trans hupper)) hn

theorem functional_tendsto_zero_of_sublinear_sums (v : Γ → E) (B : ℕ → ℝ)
    (hB : ∀ n (e : Fin n ↪ Γ) (a : Fin n → 𝕜), (∀ i, ‖a i‖ ≤ 1) →
      ‖∑ i, a i • v (e i)‖ ≤ B n)
    (hgrowth : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∃ n, M * B n < n * ε)
    (φ : E →L[𝕜] 𝕜) : Tendsto (fun γ => φ (v γ)) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(finite_large_functional_of_sublinear_sums v B hB hgrowth φ hε).compl_mem_cofinite]
    with γ hγ
  simpa only [dist_zero_right, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hγ

theorem finite_large_of_ellOne_equiv_weak_null
    (d : E ≃L[𝕜] lp (fun _ : I => 𝕜) 1) (v : Γ → E)
    (hv : ∀ φ : E →L[𝕜] 𝕜, Tendsto (fun γ => φ (v γ)) cofinite (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : {γ | ε ≤ ‖v γ‖}.Finite := by
  classical
  by_contra h
  let A : Set Γ := {γ | ε ≤ ‖v γ‖}
  have hA : A.Infinite := h
  let e : ℕ ↪ Γ := (hA.natEmbedding A).trans (Function.Embedding.subtype A)
  have he : Tendsto e atTop cofinite := e.injective.tendsto_cofinite.mono_left atTop_le_cofinite
  have ht := scalar_schur_of_equiv_ellOne d (fun n => v (e n)) (fun φ => (hv φ).comp he)
  have hn : Tendsto (fun n => ‖v (e n)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using ht.norm
  obtain ⟨n, hn⟩ := (hn.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hA.natEmbedding A n).property) hn

theorem countable_support_of_ellOne_equiv_weak_null
    (d : E ≃L[𝕜] lp (fun _ : I => 𝕜) 1) (v : Γ → E)
    (hv : ∀ φ : E →L[𝕜] 𝕜, Tendsto (fun γ => φ (v γ)) cofinite (𝓝 0)) :
    (Function.support v).Countable := by
  let A : Set Γ := ⋃ n : ℕ, {γ | 1 / ((n : ℝ) + 1) ≤ ‖v γ‖}
  have hA : A.Countable := Set.countable_iUnion (fun n =>
    (finite_large_of_ellOne_equiv_weak_null d v hv (show 0 < 1 / ((n : ℝ) + 1) by positivity)).countable)
  apply hA.mono
  intro γ hγ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hγ)
  exact Set.mem_iUnion.mpr ⟨n, hn.le⟩

end ThesisCommon
