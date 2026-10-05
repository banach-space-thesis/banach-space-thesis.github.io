import ThesisCommon.Analysis.SelfSimilarDiagonalReduction
import ThesisCommon.Analysis.SequenceTailDiagonal
import ThesisCommon.Analysis.IncreasingCoordinateChoice
import ThesisCommon.Analysis.SelfSimilarBackwardSelection
import ThesisCommon.Analysis.SelfSimilarUpperTriangular

/-! UPFP Proposition 5.4, with increasing outer and inner coordinates and
the actual diagonal of the point compression. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The c₀ case of the self-similar diagonal reduction. -/
theorem cZero_lp_diagonal_reduction (hp : p ≠ ∞)
    (T : CZeroSum (lp (fun _ : ℕ => X) p) →L[𝕜]
      CZeroSum (lp (fun _ : ℕ => X) p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ ↪ ℕ) (m : ℕ → ℕ), StrictMono n ∧ StrictMono m ∧
      ‖((cZeroPointRead p n m).comp T).comp (cZeroPointInsert p n m) -
        cZeroDiagonalPart (((cZeroPointRead p n m).comp T).comp (cZeroPointInsert p n m))‖ < ε := by
  obtain ⟨e, b, he, hb⟩ := cZero_lp_backward_selection p hp T
    (fun _ => ε / 4) (fun _ => by positivity)
  let U := cZeroBlockRead e (fun k => lpRestrict (𝕜 := 𝕜) (X := X) p (b k))
    (fun k => norm_lpRestrict_le (b k))
  let V := cZeroBlockInsert e (fun k => lpExtend (𝕜 := 𝕜) (X := X) p (b k))
    (fun k => norm_lpExtend_le (b k))
  let S := (U.comp T).comp V
  have hS : ∀ k, ‖((cZeroCoordinate k).comp S).comp
      (cZeroExtend (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ ε / 4 := by
    intro k
    exact (cZeroBlockCompression_tail_bound T e _ _ _ _ k).trans (hb k).le
  obtain ⟨f, a, hf, ha⟩ := cZero_lp_upper_triangular p hp S (show 0 < ε / 4 by positivity)
  obtain ⟨t, ht⟩ := increasing_choice_from_embeddings (fun j => (a j).trans (b (f j)))
  let c : ℕ → ℕ := fun j => a j (t j)
  let W := cZeroPointRead (𝕜 := 𝕜) (X := X) p f c
  let Z := cZeroPointInsert (𝕜 := 𝕜) (X := X) p f c
  let R := (W.comp S).comp Z
  have htail : ∀ k, ‖((cZeroCoordinate k).comp R).comp
      (cZeroExtend (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ ε / 4 := by
    intro k
    exact cZeroBlockCompression_preserves_tail_bound S f hf _ _ _ _ hS k
  have hearlier : ∀ j, (∑ i ∈ Finset.range j, ‖cZeroEntry R j i‖) ≤ ε / 4 := by
    intro j
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (ha j).le
    change ‖cZeroEntry (((cZeroBlockRead f _ _).comp S).comp (cZeroBlockInsert f _ _)) j i‖ ≤ _
    rw [cZeroEntry_block_compression]
    exact (norm_lp_selected_entry_le p (cZeroEntry S (f j) (f i)) (a j) (t j) (c i)).trans_eq
      rfl
  have hsmall : ‖R - cZeroDiagonalPart R‖ < ε := by
    apply lt_of_le_of_lt (cZero_norm_sub_diagonal_le_of_tail R
      (by positivity) (by positivity) hearlier htail)
    linarith
  refine ⟨f.trans e, (fun j => b (f j) (c j)), he.comp hf, ht, ?_⟩
  have hW : W.comp U = cZeroPointRead p (f.trans e) (fun j => b (f j) (c j)) :=
    cZeroPointRead_comp_block p e f b c
  have hZ : V.comp Z = cZeroPointInsert p (f.trans e) (fun j => b (f j) (c j)) :=
    cZeroBlockInsert_comp_point p e f b c
  have hR : R = ((W.comp U).comp T).comp (V.comp Z) := by
    dsimp [R, S]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hR, hW, hZ] at hsmall
  exact hsmall

end ThesisCommon


