import ThesisCommon.Analysis.EllOneForwardSelection
import ThesisCommon.Analysis.EllOneBackwardSelection
import ThesisCommon.Analysis.EllOneColumnNorm
import ThesisCommon.Analysis.SequenceBlockColumnBounds
import ThesisCommon.Analysis.SequencePointRetractions
import ThesisCommon.Analysis.IncreasingCoordinateChoice
import ThesisCommon.Analysis.CotypeUpperTriangular

/-! UPFP Proposition 5.2 for lp inner spaces, including infinity.
The finite earlier-column sum and whole future-column tail are controlled
separately, exactly as in the manuscript. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem norm_lp_selected_input_entry_le
    (R : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    (a : ℕ ↪ ℕ) (t c : ℕ) :
    ‖((lpCoordinate p c).comp R).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p (a t))‖ ≤ ‖R.comp (lpExtend p a)‖ := by
  have heq : lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p (a t) =
      (lpExtend p a).comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p t) := by
    ext x k
    exact (congrArg (fun z : lp (fun _ : ℕ => X) p => z k)
      (lpExtend_single (𝕜 := 𝕜) (p := p) a t x)).symm
  rw [heq, ← ContinuousLinearMap.comp_assoc]
  apply (norm_comp_right_contraction _ _ (norm_lpSingleCLM_le t)).trans
  rw [ContinuousLinearMap.comp_assoc]
  exact norm_comp_left_contraction _ (norm_lpCoordinate_le p c) _

theorem ellOne_lp_diagonal_reduction (hp : p = ∞ ∨ 1 < p.toReal)
    (T : EllOneSum ℕ (lp (fun _ : ℕ => X) p) →L[𝕜] EllOneSum ℕ (lp (fun _ : ℕ => X) p))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ ↪ ℕ) (m : ℕ → ℕ), StrictMono n ∧ StrictMono m ∧
      ‖((lpPointRead p 1 n m).comp T).comp (lpPointInsert p 1 n m) -
        lpDiagonalPart (((lpPointRead p 1 n m).comp T).comp (lpPointInsert p 1 n m))‖ < ε := by
  obtain ⟨e, b, he, hb⟩ := ellOne_lp_forward_selection p hp T
    (fun k => (ε/4) * (1/2 : ℝ)^k) (fun _ => by positivity)
  let U := lpBlockRead 1 e (fun k => lpRestrict (𝕜 := 𝕜) (X := X) p (b k))
    (fun k => norm_lpRestrict_le (b k))
  let V := lpBlockInsert 1 e (fun k => lpExtend (𝕜 := 𝕜) (X := X) p (b k))
    (fun k => norm_lpExtend_le (b k))
  let S := (U.comp T).comp V
  have hS : ∀ j, ‖((lpRestrict 1 (coordinateTail (Function.Embedding.refl ℕ) j)).comp S).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => lp (fun _ : ℕ => X) p) 1 j)‖ ≤ ε/4 := by
    intro j
    apply (lpBlockCompression_column_tail_bound 1 T e _ _ _ _ j).trans
    apply (hb j).le.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1))
      (show 0 ≤ ε/4 by positivity)
  obtain ⟨f, a, hf, ha⟩ := ellOne_lp_backward_selection p hp S
    (fun i => ((ε/4)/4) * (1/2 : ℝ)^i) (fun _ => by positivity)
  obtain ⟨t, ht⟩ := increasing_choice_from_embeddings (fun j => (a j).trans (b (f j)))
  let c : ℕ → ℕ := fun j => a j (t j)
  let W := lpPointRead (𝕜 := 𝕜) (X := X) p 1 f c
  let Z := lpPointInsert (𝕜 := 𝕜) (X := X) p 1 f c
  let R := (W.comp S).comp Z
  have htail : ∀ j, ‖((lpRestrict 1 (coordinateTail (Function.Embedding.refl ℕ) j)).comp R).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 j)‖ ≤ ε/4 := by
    intro j
    exact lpBlockCompression_preserves_column_tail_bound 1 S f hf _ _ _ _ hS j
  have hentry : ∀ i j, i < j → ‖lpEntry R i j‖ < ((ε/4)/4) * (1/2 : ℝ)^i := by
    intro i j hij
    change ‖lpEntry (((lpBlockRead 1 f _ _).comp S).comp (lpBlockInsert 1 f _ _)) i j‖ < _
    rw [lpEntry_block_compression]
    exact (norm_lp_selected_input_entry_le p (lpEntry S (f i) (f j)) (a j) (t j) (c i)).trans_lt
      (ha i j hij)
  have hearlier : ∀ j, (∑ i ∈ Finset.range j, ‖lpEntry R i j‖) ≤ ε/4 :=
    fun j => (sum_lt_of_geometric_entries (show 0 < ε/4 by positivity) _ hentry j).le
  have hsmall : ‖R - lpDiagonalPart R‖ < ε := by
    apply lt_of_le_of_lt (ellOne_norm_sub_diagonal_le_of_tail R
      (by positivity) (by positivity) hearlier htail)
    linarith
  refine ⟨f.trans e, (fun j => b (f j) (c j)), he.comp hf, ht, ?_⟩
  have hW : W.comp U = lpPointRead p 1 (f.trans e) (fun j => b (f j) (c j)) :=
    lpPointRead_comp_block p 1 e f b c
  have hZ : V.comp Z = lpPointInsert p 1 (f.trans e) (fun j => b (f j) (c j)) :=
    lpBlockInsert_comp_point p 1 e f b c
  have hR : R = ((W.comp U).comp T).comp (V.comp Z) := by
    dsimp [R, S]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hR, hW, hZ] at hsmall
  exact hsmall

end ThesisCommon
