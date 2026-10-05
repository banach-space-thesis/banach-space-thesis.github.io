import ThesisCommon.Analysis.CZeroLpForward
import ThesisCommon.Analysis.InfiniteFusionLabels
import ThesisCommon.Analysis.SequenceRestrictionAlgebra

/-! LPCK Lemma 3.10: nested selection of strictly increasing outer and
inner coordinates, controlling the whole future output tail of each column. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_cZero_upper_selection (hp : p ≠ ∞)
    (T : lp (fun _ : ℕ => CZeroSum X) p →L[𝕜] lp (fun _ : ℕ => CZeroSum X) p)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (m : ℕ → ℕ), StrictMono e ∧ StrictMono m ∧ ∀ k,
      ‖((lpRestrict p (coordinateTail e k)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => CZeroSum X) p (e k)))).comp
          (cZeroSingleCLM (m k))‖ < δ k := by
  classical
  let col := fun n => T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => CZeroSum X) p n)
  let Q : ℕ → ℕ → ℕ → Set ℕ → Prop := fun k n m B =>
    ∃ g : ℕ ↪ ℕ, Set.range g = B ∧
      ‖((lpRestrict p g).comp (col n)).comp (cZeroSingleCLM m)‖ < δ k
  have step : ∀ k (A : Set ℕ), A.Infinite → ∀ b : ℕ,
      ∃ n ∈ A, ∃ m, b < m ∧ ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
        (∀ t ∈ B, n < t) ∧ Q k n m B := by
    intro k A hA b
    obtain ⟨n, hn⟩ := hA.nonempty
    let L := {t ∈ A | n < t}
    have hL : L.Infinite := infinite_above hA n
    let a : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
    obtain ⟨m, g, hm, hg⟩ := cZero_to_lp_forward_coordinate hp
      ((lpRestrict p a).comp (col n)) b (hδ k)
    refine ⟨n, hn, m, hm, Set.range (g.trans a),
      Set.infinite_range_of_injective (g.trans a).injective, ?_, ?_, ?_⟩
    · rintro t ⟨i, rfl⟩
      exact (hL.natEmbedding L (g i)).property.1
    · rintro t ⟨i, rfl⟩
      exact (hL.natEmbedding L (g i)).property.2
    · refine ⟨g.trans a, rfl, ?_⟩
      simpa only [← lpRestrict_comp, ContinuousLinearMap.comp_assoc] using hg
  obtain ⟨f, m, A, hf, hm, _, hQ, htail⟩ := infinite_fusion_increasing_labels Q
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) step
  let e : ℕ ↪ ℕ := ⟨f, hf.injective⟩
  choose g hg hsmall using hQ
  refine ⟨e, m, hf, hm, ?_⟩
  intro k
  change ‖((lpRestrict p (coordinateTail e k)).comp (col (e k))).comp (cZeroSingleCLM (m k))‖ < δ k
  rw [ContinuousLinearMap.comp_assoc]
  apply (norm_lpRestrict_comp_le_of_range_subset ((col (e k)).comp (cZeroSingleCLM (m k)))
    (g k) (coordinateTail e k) ?_).trans_lt (hsmall k)
  rintro t ⟨j, rfl⟩
  rw [hg k]
  exact htail k (k+1+j) (by omega)

end ThesisCommon
