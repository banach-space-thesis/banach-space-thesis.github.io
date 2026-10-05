import ThesisCommon.Analysis.CompactStrongForward
import ThesisCommon.Analysis.SequenceEmbeddingAlgebra
import ThesisCommon.Analysis.SequenceEntryOperators

/-! LPCK Lemma 3.3 for finite-p sums. Nested infinite sets preserve a
summable bound on all later rows of every earlier selected column. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_forward_column_selection_of_scalar_compact (hp : p ≠ ∞)
    (hcompact : ∀ S : X →L[𝕜] lp (fun _ : ℕ => 𝕜) p, IsCompactOperator S)
    (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ k,
      Summable (fun j => ‖lpEntry T (e (k+1+j)) (e k)‖) ∧
      (∑' j, ‖lpEntry T (e (k+1+j)) (e k)‖) < δ k := by
  classical
  let col := fun n => T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p n)
  let Q : ℕ → ℕ → Set ℕ → Prop := fun k n B =>
    ∃ g : ℕ ↪ ℕ, Set.range g = B ∧
      Summable (fun j => ‖(lpCoordinate p (g j)).comp (col n)‖) ∧
      (∑' j, ‖(lpCoordinate p (g j)).comp (col n)‖) < δ k
  have step : ∀ k (A : Set ℕ), A.Infinite → ∃ n ∈ A, ∃ B : Set ℕ,
      B.Infinite ∧ B ⊆ A ∧ (∀ m ∈ B, n < m) ∧ Q k n B := by
    intro k A hA
    obtain ⟨n, hn⟩ := hA.nonempty
    obtain ⟨g, _, hmem, hsum, hsmall⟩ := lp_strong_forward_of_scalar_compact
      hp hcompact (col n) (infinite_above hA n) (hδ k)
    refine ⟨n, hn, Set.range g, Set.infinite_range_of_injective g.injective, ?_, ?_,
      g, rfl, hsum, hsmall⟩
    · rintro m ⟨j, rfl⟩
      exact (hmem j).1
    · rintro m ⟨j, rfl⟩
      exact (hmem j).2
  obtain ⟨f, A, _, _, _, _, _, hmono, hQ, htail⟩ :=
    infinite_fusion Q (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) step
  let e : ℕ ↪ ℕ := ⟨f, hmono.injective⟩
  choose g hg hs hsmall using hQ
  refine ⟨e, hmono, ?_⟩
  intro k
  have hsub : Set.range (coordinateTail e k) ⊆ Set.range (g k) := by
    rintro m ⟨j, rfl⟩
    rw [hg k]
    exact htail k (k+1+j) (by omega)
  obtain ⟨c, hc⟩ := exists_embedding_factor (g k) (coordinateTail e k) hsub
  have heq : (fun j => ‖lpEntry T (e (k+1+j)) (e k)‖) =
      (fun j => ‖(lpCoordinate p (g k (c j))).comp (col (e k))‖) := by
    funext j
    have hj : g k (c j) = e (k+1+j) := congrArg (fun a : ℕ ↪ ℕ => a j) hc
    simp only [hj, lpEntry, col, ContinuousLinearMap.comp_assoc]
  rw [heq]
  have hsum := (hs k).comp_injective c.injective
  refine ⟨hsum, ?_⟩
  apply (Summable.tsum_le_tsum_of_inj c c.injective
    (fun j _ => norm_nonneg ((lpCoordinate p (g k j)).comp (col (e k))))
    (fun _ => le_rfl) hsum (hs k)).trans_lt (hsmall k)

end ThesisCommon
