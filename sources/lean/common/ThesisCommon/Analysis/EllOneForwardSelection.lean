import ThesisCommon.Analysis.EllOneSelfSimilarSmallBlocks
import ThesisCommon.Analysis.SequenceRestrictionAlgebra
import ThesisCommon.Analysis.InfiniteFusion

/-! UPFP Proposition 3.3: recursion from the ell1 forward small-block lemma.
The conclusion controls the entire selected output tail of each column. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem ellOne_forward_selection (J : (ℕ ↪ ℕ) → X →L[𝕜] X)
    (hforward : ∀ (S : X →L[𝕜] EllOneSum ℕ Y) (ε : ℝ), 0 < ε →
      ∃ a m : ℕ ↪ ℕ, ‖((lpRestrict 1 m).comp S).comp (J a)‖ < ε)
    (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ Y) (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ k,
      ‖((lpRestrict 1 (coordinateTail e k)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 (e k)))).comp (J (a k))‖ < δ k := by
  classical
  let col := fun n => T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 n)
  let Q : ℕ → ℕ → Set ℕ → Prop := fun k n B =>
    ∃ a g : ℕ ↪ ℕ, Set.range g = B ∧ ‖((lpRestrict 1 g).comp (col n)).comp (J a)‖ < δ k
  have step : ∀ k (A : Set ℕ), A.Infinite →
      ∃ n ∈ A, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ (∀ m ∈ B, n < m) ∧ Q k n B := by
    intro k A hA
    obtain ⟨n, hn⟩ := hA.nonempty
    let L := {m ∈ A | n < m}
    have hL : L.Infinite := infinite_above hA n
    let e : ℕ ↪ ℕ := (hL.natEmbedding L).trans (Function.Embedding.subtype L)
    obtain ⟨a, f, hf⟩ := hforward ((lpRestrict 1 e).comp (col n)) (δ k) (hδ k)
    refine ⟨n, hn, Set.range (f.trans e), Set.infinite_range_of_injective
      (f.trans e).injective, ?_, ?_, ?_⟩
    · rintro m ⟨j, rfl⟩
      exact (hL.natEmbedding L (f j)).property.1
    · rintro m ⟨j, rfl⟩
      exact (hL.natEmbedding L (f j)).property.2
    · refine ⟨a, f.trans e, rfl, ?_⟩
      simpa only [← lpRestrict_comp, ContinuousLinearMap.comp_assoc] using hf
  obtain ⟨f, A, _hzero, _hinf, _hmem, _hnest, _horder, hmono, hQ, htail⟩ :=
    infinite_fusion Q (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) step
  let e : ℕ ↪ ℕ := ⟨f, hmono.injective⟩
  choose a g hg hsmall using hQ
  refine ⟨e, a, hmono, ?_⟩
  intro k
  change ‖((lpRestrict 1 (coordinateTail e k)).comp (col (e k))).comp (J (a k))‖ < δ k
  rw [ContinuousLinearMap.comp_assoc]
  apply (norm_lpRestrict_comp_le_of_range_subset ((col (e k)).comp (J (a k)))
    (g k) (coordinateTail e k) ?_).trans_lt (hsmall k)
  rintro m ⟨j, rfl⟩
  rw [hg k]
  exact htail k (k+1+j) (by omega)

/-- The whole future-column estimate for every allowed lp inner exponent. -/
theorem ellOne_lp_forward_selection (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p = ∞ ∨ 1 < p.toReal)
    (T : EllOneSum ℕ (lp (fun _ : ℕ => X) p) →L[𝕜] EllOneSum ℕ (lp (fun _ : ℕ => X) p))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ k,
      ‖((lpRestrict 1 (coordinateTail e k)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => lp (fun _ : ℕ => X) p) 1 (e k)))).comp
          (lpExtend p (a k))‖ < δ k := by
  apply ellOne_forward_selection (fun a => lpExtend p a) _ T δ hδ
  intro S ε hε
  rcases hp with rfl | hp
  · exact infinity_to_ellOne_forward_reduction S hε
  · exact lp_to_ellOne_forward_reduction p hp S hε

/-- Proposition 3.3 for a c₀ inner space. -/
theorem ellOne_cZero_forward_selection
    (T : EllOneSum ℕ (CZeroSum X) →L[𝕜] EllOneSum ℕ (CZeroSum X))
    (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ k,
      ‖((lpRestrict 1 (coordinateTail e k)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => CZeroSum X) 1 (e k)))).comp
          (cZeroExtend (a k))‖ < δ k := by
  exact ellOne_forward_selection (𝕜 := 𝕜) (X := CZeroSum X) (Y := CZeroSum X)
    (fun a => cZeroExtend (𝕜 := 𝕜) (X := X) a)
    (fun S _ hε => cZero_to_ellOne_forward_reduction S hε) T δ hδ

end ThesisCommon

