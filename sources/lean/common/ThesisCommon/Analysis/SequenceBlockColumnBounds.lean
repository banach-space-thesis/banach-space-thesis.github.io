import ThesisCommon.Analysis.SequenceBlockTailBounds

/-! Output-tail column bounds survive increasing block compressions.
These are the column counterparts of the whole-input-tail row estimates. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (q : ℝ≥0∞) [Fact (1 ≤ q)]

theorem lpBlockCompression_column_tail_bound
    (T : lp (fun _ : ℕ => Y) q →L[𝕜] lp (fun _ : ℕ => Y) q)
    (e : ℕ ↪ ℕ) (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) (j : ℕ) :
    ‖((lpRestrict q (coordinateTail (Function.Embedding.refl ℕ) j)).comp
      (((lpBlockRead q e F hF).comp T).comp (lpBlockInsert q e G hG))).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) q j)‖ ≤
    ‖((lpRestrict q (coordinateTail e j)).comp
      (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => Y) q (e j)))).comp (G j)‖ := by
  let s := coordinateTail (Function.Embedding.refl ℕ) j
  have heq : ((lpRestrict q s).comp
      (((lpBlockRead q e F hF).comp T).comp (lpBlockInsert q e G hG))).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) q j) =
      (lpDiagonal q (fun i => F (s i)) 1 zero_le_one (fun i => hF (s i))).comp
        (((lpRestrict q (coordinateTail e j)).comp
          (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => Y) q (e j)))).comp (G j)) := by
    ext x i
    change F (s i) (T (lpBlockInsert q e G hG (lp.single q j x)) (e (s i))) =
      F (s i) (T (lp.single q (e j) (G j x)) (e (s i)))
    rw [lpBlockInsert_single]
  rw [heq]
  exact norm_comp_left_contraction _ (norm_lpDiagonal_le _ 1 zero_le_one _) _

theorem lpBlockCompression_preserves_column_tail_bound
    (T : lp (fun _ : ℕ => Y) q →L[𝕜] lp (fun _ : ℕ => Y) q)
    (e : ℕ ↪ ℕ) (he : StrictMono e)
    (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) {b : ℝ}
    (hT : ∀ j, ‖((lpRestrict q (coordinateTail (Function.Embedding.refl ℕ) j)).comp T).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => Y) q j)‖ ≤ b) (j : ℕ) :
    ‖((lpRestrict q (coordinateTail (Function.Embedding.refl ℕ) j)).comp
      (((lpBlockRead q e F hF).comp T).comp (lpBlockInsert q e G hG))).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) q j)‖ ≤ b := by
  apply (lpBlockCompression_column_tail_bound q T e F G hF hG j).trans
  apply (norm_comp_right_contraction _ _ (hG j)).trans
  exact (norm_lpRestrict_comp_le_of_range_subset
    (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => Y) q (e j)))
    (coordinateTail (Function.Embedding.refl ℕ) (e j)) (coordinateTail e j)
    (coordinateTail_range_subset e he j)).trans (hT (e j))

end ThesisCommon
