import ThesisCommon.Analysis.IntervalRetractions
import ThesisCommon.Analysis.InfiniteFusion

/-! LPCK 3.13 for the unit interval: recursive row and closed-copy selection.
The estimate concerns each row on its entire selected future input tail. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem interval_lp_backward_selection (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => IntervalContinuous 𝕜) p →L[𝕜] lp (fun _ : ℕ => IntervalContinuous 𝕜) p)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (c : ℕ → NondegenerateUnitSubinterval), StrictMono e ∧ ∀ k,
      ‖((intervalRead (c k)).comp ((lpCoordinate p (e k)).comp T)).comp
        (lpExtend p (coordinateTail e k))‖ ≤ δ k := by
  classical
  let row := fun n => (lpCoordinate p n).comp T
  let Q : ℕ → ℕ → Set ℕ → Prop := fun k n B =>
    ∃ (c : NondegenerateUnitSubinterval) (g : ℕ ↪ ℕ), Set.range g = B ∧
      ‖((intervalRead c).comp (row n)).comp (lpExtend p g)‖ ≤ δ k
  have step : ∀ k (A : Set ℕ), A.Infinite → ∃ n ∈ A, ∃ B : Set ℕ,
      B.Infinite ∧ B ⊆ A ∧ (∀ m ∈ B, n < m) ∧ Q k n B := by
    intro k A hA
    obtain ⟨n, hn⟩ := hA.nonempty
    let L := {m ∈ A | n < m}
    have hL : L.Infinite := infinite_above hA n
    let a : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
    obtain ⟨g, c, hs⟩ := interval_backward_retraction hp ((row n).comp (lpExtend p a)) (hδ k)
    refine ⟨n, hn, Set.range (g.trans a), Set.infinite_range_of_injective
      (g.trans a).injective, ?_, ?_, c, g.trans a, rfl, ?_⟩
    · rintro m ⟨j, rfl⟩
      exact (hL.natEmbedding L (g j)).property.1
    · rintro m ⟨j, rfl⟩
      exact (hL.natEmbedding L (g j)).property.2
    · simpa only [← lpExtend_comp, ContinuousLinearMap.comp_assoc] using hs
  obtain ⟨f, A, _, _, _, _, _, hf, hQ, htail⟩ :=
    infinite_fusion Q (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) step
  let e : ℕ ↪ ℕ := ⟨f, hf.injective⟩
  choose c g hg hs using hQ
  refine ⟨e, c, hf, ?_⟩
  intro k
  apply (norm_comp_lpExtend_le_of_range_subset ((intervalRead (c k)).comp (row (e k)))
    (g k) (coordinateTail e k) ?_).trans (hs k)
  rintro m ⟨j, rfl⟩
  rw [hg k]
  exact htail k (k+1+j) (by omega)

end ThesisCommon
