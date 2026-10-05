import ThesisCommon.Analysis.SequencePointRetractions
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

theorem norm_lp_selected_entry_le (R : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    (a : ℕ ↪ ℕ) (t c : ℕ) :
    ‖((lpCoordinate p (a t)).comp R).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p c)‖ ≤ ‖(lpRestrict p a).comp R‖ := by
  have heq : lpCoordinate (𝕜 := 𝕜) (X := X) p (a t) =
      (lpCoordinate p t).comp (lpRestrict p a) := by ext x; rfl
  rw [heq]
  apply (norm_comp_right_contraction _ _ (norm_lpSingleCLM_le c)).trans
  rw [ContinuousLinearMap.comp_assoc]
  exact norm_comp_left_contraction _ (norm_lpCoordinate_le p t) _

/-- The infinity case of the self-similar diagonal reduction. -/
theorem infinity_lp_diagonal_reduction (hp : p ≠ ∞)
    (T : EllInfinitySum (lp (fun _ : ℕ => X) p) →L[𝕜]
      EllInfinitySum (lp (fun _ : ℕ => X) p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ ↪ ℕ) (m : ℕ → ℕ), StrictMono n ∧ StrictMono m ∧
      ‖((lpPointRead p ∞ n m).comp T).comp (lpPointInsert p ∞ n m) -
        lpDiagonalPart (((lpPointRead p ∞ n m).comp T).comp (lpPointInsert p ∞ n m))‖ < ε := by
  obtain ⟨e, b, he, hb⟩ := infinity_lp_backward_selection p hp T
    (fun _ => ε / 4) (fun _ => by positivity)
  let U := lpBlockRead ∞ e (fun k => lpRestrict (𝕜 := 𝕜) (X := X) p (b k))
    (fun k => norm_lpRestrict_le (b k))
  let V := lpBlockInsert ∞ e (fun k => lpExtend (𝕜 := 𝕜) (X := X) p (b k))
    (fun k => norm_lpExtend_le (b k))
  let S := (U.comp T).comp V
  have hS : ∀ k, ‖((lpCoordinate ∞ k).comp S).comp
      (lpExtend ∞ (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ ε / 4 := by
    intro k
    exact (lpBlockCompression_tail_bound ∞ T e _ _ _ _ k).trans (hb k).le
  obtain ⟨f, a, hf, ha⟩ := infinity_lp_upper_triangular p hp S (show 0 < ε / 4 by positivity)
  obtain ⟨t, ht⟩ := increasing_choice_from_embeddings (fun j => (a j).trans (b (f j)))
  let c : ℕ → ℕ := fun j => a j (t j)
  let W := lpPointRead (𝕜 := 𝕜) (X := X) p ∞ f c
  let Z := lpPointInsert (𝕜 := 𝕜) (X := X) p ∞ f c
  let R := (W.comp S).comp Z
  have htail : ∀ k, ‖((lpCoordinate ∞ k).comp R).comp
      (lpExtend ∞ (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ ε / 4 := by
    intro k
    exact lpBlockCompression_preserves_tail_bound S f hf _ _ _ _ hS k
  have hearlier : ∀ j, (∑ i ∈ Finset.range j, ‖lpEntry R j i‖) ≤ ε / 4 := by
    intro j
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (ha j).le
    change ‖lpEntry (((lpBlockRead ∞ f _ _).comp S).comp (lpBlockInsert ∞ f _ _)) j i‖ ≤ _
    rw [lpEntry_block_compression]
    exact (norm_lp_selected_entry_le p (lpEntry S (f j) (f i)) (a j) (t j) (c i)).trans_eq
      rfl
  have hsmall : ‖R - lpDiagonalPart R‖ < ε := by
    apply lt_of_le_of_lt (infinity_norm_sub_diagonal_le_of_tail R
      (by positivity) (by positivity) hearlier htail)
    linarith
  refine ⟨f.trans e, (fun j => b (f j) (c j)), he.comp hf, ht, ?_⟩
  have hW : W.comp U = lpPointRead p ∞ (f.trans e) (fun j => b (f j) (c j)) :=
    lpPointRead_comp_block p ∞ e f b c
  have hZ : V.comp Z = lpPointInsert p ∞ (f.trans e) (fun j => b (f j) (c j)) :=
    lpBlockInsert_comp_point p ∞ e f b c
  have hR : R = ((W.comp U).comp T).comp (V.comp Z) := by
    dsimp [R, S]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hR, hW, hZ] at hsmall
  exact hsmall

end ThesisCommon

