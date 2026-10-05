import ThesisCommon.Analysis.SequenceBlockTailBounds

/-! Point retractions from a double sequence to one coefficient per selected
outer row. All maps act on the actual sequence spaces. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]

def lpPointRead (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) q →L[𝕜] lp (fun _ : ℕ => X) q :=
  lpBlockRead q n (fun j => lpCoordinate p (m j)) (fun j => norm_lpCoordinate_le p (m j))

def lpPointInsert (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    lp (fun _ : ℕ => X) q →L[𝕜] lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) q :=
  lpBlockInsert q n (fun j => lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p (m j))
    (fun j => norm_lpSingleCLM_le (p := p) (m j))

theorem norm_lpPointRead_le (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    ‖lpPointRead (𝕜 := 𝕜) (X := X) p q n m‖ ≤ 1 := norm_lpBlockRead_le ..

theorem norm_lpPointInsert_le (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    ‖lpPointInsert (𝕜 := 𝕜) (X := X) p q n m‖ ≤ 1 := norm_lpBlockInsert_le ..

theorem lpPointRead_comp_insert (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    (lpPointRead (𝕜 := 𝕜) (X := X) p q n m).comp (lpPointInsert p q n m) =
      ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => X) q) := by
  apply lpBlockRead_comp_insert
  intro k
  ext x
  simp

theorem lpPointRead_comp_block (e f : ℕ ↪ ℕ) (b : ℕ → (ℕ ↪ ℕ)) (c : ℕ → ℕ) :
    (lpPointRead (𝕜 := 𝕜) (X := X) p q f c).comp
      (lpBlockRead q e (fun j => lpRestrict p (b j)) (fun j => norm_lpRestrict_le (b j))) =
    lpPointRead p q (f.trans e) (fun j => b (f j) (c j)) := by
  ext x k
  rfl

theorem lpBlockInsert_comp_point (e f : ℕ ↪ ℕ) (b : ℕ → (ℕ ↪ ℕ)) (c : ℕ → ℕ) :
    (lpBlockInsert q e (fun j => lpExtend (𝕜 := 𝕜) (X := X) p (b j))
      (fun j => norm_lpExtend_le (b j))).comp (lpPointInsert p q f c) =
    lpPointInsert p q (f.trans e) (fun j => b (f j) (c j)) := by
  unfold lpPointInsert
  conv_lhs => arg 2; unfold lpBlockInsert
  rw [← ContinuousLinearMap.comp_assoc, lpBlockInsert_comp_extend]
  unfold lpBlockInsert
  ext x : 1
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  funext j
  change lpExtend (𝕜 := 𝕜) p (b (f j)) (lp.single p (c j) (x j)) =
    lp.single p (b (f j) (c j)) (x j)
  exact lpExtend_single (p := p) (b (f j)) (c j) (x j)

omit [Fact (1 ≤ q)] in
def cZeroPointRead (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    CZeroSum (lp (fun _ : ℕ => X) p) →L[𝕜] CZeroSum X :=
  cZeroBlockRead n (fun j => lpCoordinate p (m j)) (fun j => norm_lpCoordinate_le p (m j))

omit [Fact (1 ≤ q)] in
def cZeroPointInsert (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    CZeroSum X →L[𝕜] CZeroSum (lp (fun _ : ℕ => X) p) :=
  cZeroBlockInsert n (fun j => lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p (m j))
    (fun j => norm_lpSingleCLM_le (p := p) (m j))

omit [Fact (1 ≤ q)] in
theorem norm_cZeroPointRead_le (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    ‖cZeroPointRead (𝕜 := 𝕜) (X := X) p n m‖ ≤ 1 := norm_cZeroBlockRead_le ..

omit [Fact (1 ≤ q)] in
theorem norm_cZeroPointInsert_le (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    ‖cZeroPointInsert (𝕜 := 𝕜) (X := X) p n m‖ ≤ 1 := norm_cZeroBlockInsert_le ..

omit [Fact (1 ≤ q)] in
theorem cZeroPointRead_comp_insert (n : ℕ ↪ ℕ) (m : ℕ → ℕ) :
    (cZeroPointRead (𝕜 := 𝕜) (X := X) p n m).comp (cZeroPointInsert p n m) =
      ContinuousLinearMap.id 𝕜 (CZeroSum X) := by
  apply cZeroBlockRead_comp_insert
  intro k
  ext x
  simp

omit [Fact (1 ≤ q)] in
theorem cZeroPointRead_comp_block (e f : ℕ ↪ ℕ) (b : ℕ → (ℕ ↪ ℕ)) (c : ℕ → ℕ) :
    (cZeroPointRead (𝕜 := 𝕜) (X := X) p f c).comp
      (cZeroBlockRead e (fun j => lpRestrict p (b j)) (fun j => norm_lpRestrict_le (b j))) =
    cZeroPointRead p (f.trans e) (fun j => b (f j) (c j)) := by
  ext x k
  rfl

omit [Fact (1 ≤ q)] in
theorem cZeroBlockInsert_comp_point (e f : ℕ ↪ ℕ) (b : ℕ → (ℕ ↪ ℕ)) (c : ℕ → ℕ) :
    (cZeroBlockInsert e (fun j => lpExtend (𝕜 := 𝕜) (X := X) p (b j))
      (fun j => norm_lpExtend_le (b j))).comp (cZeroPointInsert p f c) =
    cZeroPointInsert p (f.trans e) (fun j => b (f j) (c j)) := by
  unfold cZeroPointInsert
  conv_lhs => arg 2; unfold cZeroBlockInsert
  rw [← ContinuousLinearMap.comp_assoc, cZeroBlockInsert_comp_extend]
  unfold cZeroBlockInsert
  ext x : 1
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  ext j : 1
  change lpExtend (𝕜 := 𝕜) p (b (f j)) (lp.single p (c j) (x j)) =
    lp.single p (b (f j) (c j)) (x j)
  exact lpExtend_single (p := p) (b (f j)) (c j) (x j)

end ThesisCommon




