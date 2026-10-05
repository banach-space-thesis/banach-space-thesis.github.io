import ThesisCommon.Analysis.SelfSimilarSmallBlocks
import ThesisCommon.Analysis.SequenceEmbeddingAlgebra
import ThesisCommon.Analysis.InfiniteFusion

/-! UPFP Proposition 4.9: recursive backward selection with an inner
restriction for each retained outer row. The estimates control the whole
infinite input tail, including the action of arbitrary infinity operators.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The nested-set recursion with an additional restriction chosen at each
row. Its hypotheses concern concrete maps; both applications below supply
them from the checked coordinate algebra and one-step analytic estimate. -/
theorem backward_fusion_with_restrictions {W : Type*}
    (R : W → X →L[𝕜] X) (J : (ℕ ↪ ℕ) → Z →L[𝕜] Z)
    (hcomp : ∀ e f, (J e).comp (J f) = J (f.trans e))
    (hnorm : ∀ (T : Z →L[𝕜] X) (e f : ℕ ↪ ℕ), Set.range f ⊆ Set.range e →
      ‖T.comp (J f)‖ ≤ ‖T.comp (J e)‖)
    (row : ℕ → Z →L[𝕜] X)
    (hback : ∀ n e (ε : ℝ), 0 < ε → ∃ (a : W) (f : ℕ ↪ ℕ),
      ‖((R a).comp ((row n).comp (J e))).comp (J f)‖ < ε)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → W), StrictMono e ∧ ∀ k,
      ‖((R (a k)).comp (row (e k))).comp (J (coordinateTail e k))‖ < δ k := by
  classical
  let Q : ℕ → ℕ → Set ℕ → Prop := fun k n B =>
    ∃ (a : W) (g : ℕ ↪ ℕ), Set.range g = B ∧
      ‖((R a).comp (row n)).comp (J g)‖ < δ k
  have step : ∀ k (A : Set ℕ), A.Infinite →
      ∃ n ∈ A, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
        (∀ m ∈ B, n < m) ∧ Q k n B := by
    intro k A hA
    obtain ⟨n, hn⟩ := hA.nonempty
    let B := {m ∈ A | n < m}
    have hB : B.Infinite := infinite_above hA n
    let e : ℕ ↪ ℕ := (hB.natEmbedding B).trans (Function.Embedding.subtype B)
    obtain ⟨a, f, hf⟩ := hback n e (δ k) (hδ k)
    refine ⟨n, hn, Set.range (f.trans e), Set.infinite_range_of_injective
      (f.trans e).injective, ?_, ?_, ?_⟩
    · rintro m ⟨j, rfl⟩
      exact (hB.natEmbedding B (f j)).property.1
    · rintro m ⟨j, rfl⟩
      exact (hB.natEmbedding B (f j)).property.2
    · refine ⟨a, f.trans e, rfl, ?_⟩
      simpa only [ContinuousLinearMap.comp_assoc, hcomp] using hf
  obtain ⟨f, A, _hzero, _hinf, _hmem, _hnest, _horder, hmono, hQ, htail⟩ :=
    infinite_fusion Q (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) step
  let e : ℕ ↪ ℕ := ⟨f, hmono.injective⟩
  choose a g hg hsmall using hQ
  refine ⟨e, a, hmono, ?_⟩
  intro k
  apply lt_of_le_of_lt
    (hnorm ((R (a k)).comp (row (e k))) (g k) (coordinateTail e k) ?_) (hsmall k)
  rintro m ⟨j, rfl⟩
  rw [hg k]
  exact htail k (k + 1 + j) (by omega)

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Proposition 4.9 for infinity, strengthened to any positive row tolerances. -/
theorem infinity_lp_backward_selection (hp : p ≠ ∞)
    (T : EllInfinitySum (lp (fun _ : ℕ => X) p) →L[𝕜]
      EllInfinitySum (lp (fun _ : ℕ => X) p))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ k,
      ‖((lpRestrict p (a k)).comp ((lpCoordinate ∞ (e k)).comp T)).comp
        (lpExtend ∞ (coordinateTail e k))‖ < δ k := by
  apply backward_fusion_with_restrictions
    (fun a => lpRestrict (𝕜 := 𝕜) (X := X) p a)
    (fun e => lpExtend (𝕜 := 𝕜) (X := lp (fun _ : ℕ => X) p) ∞ e)
    (fun e f => lpExtend_comp f e) norm_comp_lpExtend_le_of_range_subset
    (fun n => (lpCoordinate ∞ n).comp T) _ δ hδ
  intro n e ε hε
  exact infinity_to_lp_backward_reduction p hp
    (((lpCoordinate ∞ n).comp T).comp (lpExtend ∞ e)) hε

/-- Proposition 4.9 for c₀, with the same whole-tail control. -/
theorem cZero_lp_backward_selection (hp : p ≠ ∞)
    (T : CZeroSum (lp (fun _ : ℕ => X) p) →L[𝕜] CZeroSum (lp (fun _ : ℕ => X) p))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ k,
      ‖((lpRestrict p (a k)).comp ((cZeroCoordinate (e k)).comp T)).comp
        (cZeroExtend (coordinateTail e k))‖ < δ k := by
  apply backward_fusion_with_restrictions
    (fun a => lpRestrict (𝕜 := 𝕜) (X := X) p a)
    (fun e => cZeroExtend (𝕜 := 𝕜) (X := lp (fun _ : ℕ => X) p) e)
    (fun e f => cZeroExtend_comp f e) norm_comp_cZeroExtend_le_of_range_subset
    (fun n => (cZeroCoordinate n).comp T) _ δ hδ
  intro n e ε hε
  exact cZero_to_lp_backward_reduction p hp
    (((cZeroCoordinate n).comp T).comp (cZeroExtend e)) hε

end ThesisCommon
