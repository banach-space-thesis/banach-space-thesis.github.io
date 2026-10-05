import ThesisCommon.Analysis.EllOneLpDiagonalReduction
import ThesisCommon.Analysis.CZeroInnerPointRetractions

/-! The c0-inner case of UPFP Proposition 5.2. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem ellOne_cZero_diagonal_reduction
    (T : EllOneSum ℕ (CZeroSum X) →L[𝕜] EllOneSum ℕ (CZeroSum X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ ↪ ℕ) (m : ℕ → ℕ), StrictMono n ∧ StrictMono m ∧
      ‖((lpCZeroPointRead 1 n m).comp T).comp (lpCZeroPointInsert 1 n m) -
        lpDiagonalPart (((lpCZeroPointRead 1 n m).comp T).comp (lpCZeroPointInsert 1 n m))‖ < ε := by
  obtain ⟨e, b, he, hb⟩ := ellOne_cZero_forward_selection T
    (fun k => (ε/4) * (1/2 : ℝ)^k) (fun _ => by positivity)
  let U := lpBlockRead 1 e (fun k => cZeroRestrict (𝕜 := 𝕜) (X := X) (b k))
    (fun k => norm_cZeroRestrict_le (b k))
  let V := lpBlockInsert 1 e (fun k => cZeroExtend (𝕜 := 𝕜) (X := X) (b k))
    (fun k => norm_cZeroExtend_le (b k))
  let S := (U.comp T).comp V
  have hS : ∀ j, ‖((lpRestrict 1 (coordinateTail (Function.Embedding.refl ℕ) j)).comp S).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => CZeroSum X) 1 j)‖ ≤ ε/4 := by
    intro j
    apply (lpBlockCompression_column_tail_bound 1 T e _ _ _ _ j).trans
    apply (hb j).le.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1))
      (show 0 ≤ ε/4 by positivity)
  obtain ⟨f, a, hf, ha⟩ := ellOne_cZero_backward_selection S
    (fun i => ((ε/4)/4) * (1/2 : ℝ)^i) (fun _ => by positivity)
  obtain ⟨t, ht⟩ := increasing_choice_from_embeddings (fun j => (a j).trans (b (f j)))
  let c : ℕ → ℕ := fun j => a j (t j)
  let W := lpCZeroPointRead (𝕜 := 𝕜) (X := X) 1 f c
  let Z := lpCZeroPointInsert (𝕜 := 𝕜) (X := X) 1 f c
  let R := (W.comp S).comp Z
  have htail : ∀ j, ‖((lpRestrict 1 (coordinateTail (Function.Embedding.refl ℕ) j)).comp R).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 j)‖ ≤ ε/4 := by
    intro j
    exact lpBlockCompression_preserves_column_tail_bound 1 S f hf _ _ _ _ hS j
  have hentry : ∀ i j, i < j → ‖lpEntry R i j‖ < ((ε/4)/4) * (1/2 : ℝ)^i := by
    intro i j hij
    change ‖lpEntry (((lpBlockRead 1 f _ _).comp S).comp (lpBlockInsert 1 f _ _)) i j‖ < _
    rw [lpEntry_block_compression]
    exact (norm_cZero_selected_input_entry_le (lpEntry S (f i) (f j)) (a j) (t j) (c i)).trans_lt
      (ha i j hij)
  have hearlier : ∀ j, (∑ i ∈ Finset.range j, ‖lpEntry R i j‖) ≤ ε/4 :=
    fun j => (sum_lt_of_geometric_entries (show 0 < ε/4 by positivity) _ hentry j).le
  have hsmall : ‖R - lpDiagonalPart R‖ < ε := by
    apply lt_of_le_of_lt (ellOne_norm_sub_diagonal_le_of_tail R
      (by positivity) (by positivity) hearlier htail)
    linarith
  refine ⟨f.trans e, (fun j => b (f j) (c j)), he.comp hf, ht, ?_⟩
  have hW : W.comp U = lpCZeroPointRead 1 (f.trans e) (fun j => b (f j) (c j)) :=
    lpCZeroPointRead_comp_block 1 e f b c
  have hZ : V.comp Z = lpCZeroPointInsert 1 (f.trans e) (fun j => b (f j) (c j)) :=
    lpBlockInsert_comp_cZeroPoint 1 e f b c
  have hR : R = ((W.comp U).comp T).comp (V.comp Z) := by
    dsimp [R, S]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hR, hW, hZ] at hsmall
  exact hsmall

end ThesisCommon

