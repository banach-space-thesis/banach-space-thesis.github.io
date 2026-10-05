import ThesisCommon.Analysis.CotypeBackward
import ThesisCommon.Analysis.SequenceCoordinates
import ThesisCommon.Analysis.SequenceEmbeddingAlgebra
import ThesisCommon.Analysis.InfiniteFusion

/-! The complete recursive selection in UPFP Proposition 4.7.
The conclusion controls each row on the whole infinite tail, so it also
applies to operators on ℓ∞ that are not determined by their matrix entries.
The construction of the approximating triangular operator is a later step.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The nested-set recursion, parameterized by concrete coordinate insertions.
The composition and norm-monotonicity assumptions are proved for lp and c₀
in SequenceEmbeddingAlgebra; the one-step estimate is the cotype lemma. -/
theorem backward_fusion_selection
    (J : (ℕ ↪ ℕ) → Z →L[𝕜] Z)
    (hcomp : ∀ e f, (J e).comp (J f) = J (f.trans e))
    (hnorm : ∀ (R : Z →L[𝕜] X) (e f : ℕ ↪ ℕ), Set.range f ⊆ Set.range e →
      ‖R.comp (J f)‖ ≤ ‖R.comp (J e)‖)
    (row : ℕ → Z →L[𝕜] X)
    (hback : ∀ n e (ε : ℝ), 0 < ε →
      ∃ f : ℕ ↪ ℕ, ‖(row n |>.comp (J e)).comp (J f)‖ < ε)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧
      ∀ k, ‖(row (e k)).comp (J (coordinateTail e k))‖ < δ k := by
  classical
  let Q : ℕ → ℕ → Set ℕ → Prop := fun k n B =>
    ∃ g : ℕ ↪ ℕ, Set.range g = B ∧ ‖(row n).comp (J g)‖ < δ k
  have step : ∀ k (A : Set ℕ), A.Infinite →
      ∃ n ∈ A, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
        (∀ m ∈ B, n < m) ∧ Q k n B := by
    intro k A hA
    obtain ⟨n, hn⟩ := hA.nonempty
    let B := {m ∈ A | n < m}
    have hB : B.Infinite := infinite_above hA n
    let e : ℕ ↪ ℕ := (hB.natEmbedding B).trans (Function.Embedding.subtype B)
    obtain ⟨f, hf⟩ := hback n e (δ k) (hδ k)
    refine ⟨n, hn, Set.range (f.trans e), Set.infinite_range_of_injective
      (f.trans e).injective, ?_, ?_, ?_⟩
    · rintro m ⟨j, rfl⟩
      exact (hB.natEmbedding B (f j)).property.1
    · rintro m ⟨j, rfl⟩
      exact (hB.natEmbedding B (f j)).property.2
    · refine ⟨f.trans e, rfl, ?_⟩
      rw [← hcomp, ← ContinuousLinearMap.comp_assoc]
      exact hf
  obtain ⟨f, A, _hzero, _hinf, _hmem, _hnest, _horder, hmono, hQ, htail⟩ :=
    infinite_fusion Q (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) step
  let e : ℕ ↪ ℕ := ⟨f, hmono.injective⟩
  refine ⟨e, hmono, ?_⟩
  intro k
  obtain ⟨g, hg, hsmall⟩ := hQ k
  apply lt_of_le_of_lt (hnorm (row (e k)) g (coordinateTail e k) ?_) hsmall
  rintro m ⟨j, rfl⟩
  rw [hg]
  exact htail k (k + 1 + j) (by omega)

/-- For every positive row tolerance, choose a strictly increasing sequence
whose entire later-coordinate restriction satisfies that tolerance in ℓ∞. -/
theorem HasFiniteCotype.infinity_backward_selection (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ k,
      ‖((lpCoordinate ∞ (e k)).comp T).comp (lpExtend ∞ (coordinateTail e k))‖ < δ k := by
  apply backward_fusion_selection
    (fun e => lpExtend (𝕜 := 𝕜) (X := X) ∞ e)
    (fun e f => lpExtend_comp f e) norm_comp_lpExtend_le_of_range_subset
    (fun n => (lpCoordinate ∞ n).comp T) _ δ hδ
  intro n e ε hε
  exact h.infinity_backward_reduction (((lpCoordinate ∞ n).comp T).comp (lpExtend ∞ e)) hε

/-- The same recursion on c₀, retaining the actual infinite-tail norm bound. -/
theorem HasFiniteCotype.cZero_backward_selection (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] CZeroSum X)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ k,
      ‖((cZeroCoordinate (e k)).comp T).comp (cZeroExtend (coordinateTail e k))‖ < δ k := by
  apply backward_fusion_selection
    (fun e => cZeroExtend (𝕜 := 𝕜) (X := X) e)
    (fun e f => cZeroExtend_comp f e) norm_comp_cZeroExtend_le_of_range_subset
    (fun n => (cZeroCoordinate n).comp T) _ δ hδ
  intro n e ε hε
  exact h.cZero_backward_reduction (((cZeroCoordinate n).comp T).comp (cZeroExtend e)) hε

end ThesisCommon
