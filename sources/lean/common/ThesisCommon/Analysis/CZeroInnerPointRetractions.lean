import ThesisCommon.Analysis.SequenceBlockTailBounds

/-! Single inner-coordinate retractions for an lp outer sum of c0 spaces. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (q : ℝ≥0∞) [Fact (1 ≤ q)]

def lpCZeroPointRead (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    lp (fun _ : ℕ => CZeroSum X) q →L[𝕜] lp (fun _ : ℕ => X) q :=
  lpBlockRead q n (fun j => cZeroCoordinate (m j)) (fun j => norm_cZeroCoordinate_le (m j))

def lpCZeroPointInsert (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    lp (fun _ : ℕ => X) q →L[𝕜] lp (fun _ : ℕ => CZeroSum X) q :=
  lpBlockInsert q n (fun j => cZeroSingleCLM (m j)) (fun j => norm_cZeroSingleCLM_le (m j))

theorem norm_lpCZeroPointRead_le (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    ‖lpCZeroPointRead (𝕜 := 𝕜) (X := X) q n m‖ ≤ 1 := norm_lpBlockRead_le ..

theorem norm_lpCZeroPointInsert_le (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    ‖lpCZeroPointInsert (𝕜 := 𝕜) (X := X) q n m‖ ≤ 1 := norm_lpBlockInsert_le ..

theorem lpCZeroPointRead_comp_insert (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    (lpCZeroPointRead (𝕜 := 𝕜) (X := X) q n m).comp (lpCZeroPointInsert q n m) =
      ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => X) q) := by
  apply lpBlockRead_comp_insert
  intro k
  ext x
  simp [cZeroSingle_apply]

theorem lpCZeroPointRead_comp_block (e f : ℕ ↪ ℕ) (b : ℕ → (ℕ ↪ ℕ)) (c : ℕ → ℕ) :
    (lpCZeroPointRead (𝕜 := 𝕜) (X := X) q f c).comp
      (lpBlockRead q e (fun j => cZeroRestrict (b j)) (fun j => norm_cZeroRestrict_le (b j))) =
    lpCZeroPointRead q (f.trans e) (fun j => b (f j) (c j)) := by
  ext x k
  rfl

theorem lpBlockInsert_comp_cZeroPoint (e f : ℕ ↪ ℕ) (b : ℕ → (ℕ ↪ ℕ)) (c : ℕ → ℕ) :
    (lpBlockInsert q e (fun j => cZeroExtend (𝕜 := 𝕜) (X := X) (b j))
      (fun j => norm_cZeroExtend_le (b j))).comp (lpCZeroPointInsert q f c) =
    lpCZeroPointInsert q (f.trans e) (fun j => b (f j) (c j)) := by
  unfold lpCZeroPointInsert
  conv_lhs => arg 2; unfold lpBlockInsert
  rw [← ContinuousLinearMap.comp_assoc, lpBlockInsert_comp_extend]
  unfold lpBlockInsert
  ext x : 1
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  funext j
  change cZeroExtend (𝕜 := 𝕜) (b (f j)) (cZeroSingle (c j) (x j)) =
    cZeroSingle (b (f j) (c j)) (x j)
  exact cZeroExtend_single (b (f j)) (c j) (x j)

omit [Fact (1 ≤ q)] in
theorem norm_cZero_selected_input_entry_le (R : CZeroSum X →L[𝕜] CZeroSum X)
    (a : ℕ ↪ ℕ) (t c : ℕ) :
    ‖((cZeroCoordinate c).comp R).comp (cZeroSingleCLM (a t))‖ ≤ ‖R.comp (cZeroExtend a)‖ := by
  have heq : cZeroSingleCLM (𝕜 := 𝕜) (X := X) (a t) =
      (cZeroExtend a).comp (cZeroSingleCLM t) := by
    ext x k
    exact (congrArg (fun z : CZeroSum X => z k) (cZeroExtend_single (𝕜 := 𝕜) a t x)).symm
  rw [heq, ← ContinuousLinearMap.comp_assoc]
  apply (norm_comp_right_contraction _ _ (norm_cZeroSingleCLM_le t)).trans
  rw [ContinuousLinearMap.comp_assoc]
  exact norm_comp_left_contraction _ (norm_cZeroCoordinate_le c) _

end ThesisCommon
