import ThesisCommon.Analysis.SequenceBlockRetractions
import ThesisCommon.Analysis.SequenceEntryAlgebra

/-! Coordinate, entry, and whole-tail identities for block compressions.
The tail identity factors through the original entire future tail and a
contraction, which is essential for operators on all bounded sequences.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (q : ℝ≥0∞) [Fact (1 ≤ q)]

theorem lpDiagonal_comp_extend (F : ℕ → X →L[𝕜] Y) (hF : ∀ k, ‖F k‖ ≤ 1) (e : ℕ ↪ ℕ) :
    (lpDiagonal q F 1 zero_le_one hF).comp (lpExtend q e) =
      (lpExtend q e).comp (lpDiagonal q (fun i => F (e i)) 1 zero_le_one (fun i => hF (e i))) := by
  ext x k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simp only [ContinuousLinearMap.comp_apply, lpDiagonal_apply, lpExtend_apply_image]
  · simp only [ContinuousLinearMap.comp_apply, lpDiagonal_apply,
      lpExtend_apply_off_range e _ hk, map_zero]

theorem lpBlockInsert_comp_extend (e : ℕ ↪ ℕ) (G : ℕ → X →L[𝕜] Y)
    (hG : ∀ k, ‖G k‖ ≤ 1) (f : ℕ ↪ ℕ) :
    (lpBlockInsert q e G hG).comp (lpExtend q f) =
      lpBlockInsert q (f.trans e) (fun i => G (f i)) (fun i => hG (f i)) := by
  unfold lpBlockInsert
  rw [ContinuousLinearMap.comp_assoc, lpDiagonal_comp_extend,
    ← ContinuousLinearMap.comp_assoc, lpExtend_comp]

theorem lpBlockInsert_single (e : ℕ ↪ ℕ) (G : ℕ → X →L[𝕜] Y)
    (hG : ∀ k, ‖G k‖ ≤ 1) (n : ℕ) (x : X) :
    lpBlockInsert q e G hG (lp.single q n x) = lp.single q (e n) (G n x) := by
  have hdiag : lpDiagonal q G 1 zero_le_one hG (lp.single q n x) = lp.single q n (G n x) := by
    ext m
    by_cases hm : m = n
    · subst m; simp
    · simp [hm]
  change lpExtend (𝕜 := 𝕜) q e (lpDiagonal q G 1 zero_le_one hG (lp.single q n x)) = _
  rw [hdiag, lpExtend_single]

theorem lpEntry_block_compression
    (T : lp (fun _ : ℕ => Y) q →L[𝕜] lp (fun _ : ℕ => Y) q)
    (e : ℕ ↪ ℕ) (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) (i j : ℕ) :
    lpEntry (((lpBlockRead q e F hF).comp T).comp (lpBlockInsert q e G hG)) i j =
      ((F i).comp (lpEntry T (e i) (e j))).comp (G j) := by
  ext x
  change F i (T (lpBlockInsert q e G hG (lp.single q j x)) (e i)) =
    F i (T (lp.single q (e j) (G j x)) (e i))
  rw [lpBlockInsert_single]

theorem lpBlockCompression_tail_bound
    (T : lp (fun _ : ℕ => Y) q →L[𝕜] lp (fun _ : ℕ => Y) q)
    (e : ℕ ↪ ℕ) (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) (k : ℕ) :
    ‖((lpCoordinate q k).comp (((lpBlockRead q e F hF).comp T).comp (lpBlockInsert q e G hG))).comp
      (lpExtend q (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤
      ‖((F k).comp ((lpCoordinate q (e k)).comp T)).comp (lpExtend q (coordinateTail e k))‖ := by
  let s := coordinateTail (Function.Embedding.refl ℕ) k
  have heq : ((lpCoordinate q k).comp
      (((lpBlockRead q e F hF).comp T).comp (lpBlockInsert q e G hG))).comp (lpExtend q s) =
        (((F k).comp ((lpCoordinate q (e k)).comp T)).comp (lpExtend q (coordinateTail e k))).comp
          (lpDiagonal q (fun i => G (s i)) 1 zero_le_one (fun i => hG (s i))) := by
    ext x
    have hx := DFunLike.congr_fun (lpBlockInsert_comp_extend q e G hG s) x
    change lpBlockInsert q e G hG (lpExtend (𝕜 := 𝕜) q s x) =
      lpExtend (𝕜 := 𝕜) q (coordinateTail e k)
        (lpDiagonal q (fun i => G (s i)) 1 zero_le_one (fun i => hG (s i)) x) at hx
    change F k (T (lpBlockInsert q e G hG (lpExtend (𝕜 := 𝕜) q s x)) (e k)) = _
    rw [hx]
    rfl
  rw [heq]
  calc
    _ ≤ ‖((F k).comp ((lpCoordinate q (e k)).comp T)).comp (lpExtend q (coordinateTail e k))‖ *
        ‖lpDiagonal q (fun i => G (s i)) 1 zero_le_one (fun i => hG (s i))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left (norm_lpDiagonal_le _ 1 zero_le_one _) (norm_nonneg _)
    _ = _ := mul_one _

theorem cZeroDiagonal_comp_extend (F : ℕ → X →L[𝕜] Y) (hF : ∀ k, ‖F k‖ ≤ 1) (e : ℕ ↪ ℕ) :
    (cZeroDiagonal F 1 zero_le_one hF).comp (cZeroExtend e) =
      (cZeroExtend e).comp (cZeroDiagonal (fun i => F (e i)) 1 zero_le_one (fun i => hF (e i))) := by
  ext x k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simp only [ContinuousLinearMap.comp_apply, cZeroDiagonal_apply, cZeroExtend_apply_image]
  · simp only [ContinuousLinearMap.comp_apply, cZeroDiagonal_apply,
      cZeroExtend_apply_off_range e _ hk, map_zero]

theorem cZeroBlockInsert_comp_extend (e : ℕ ↪ ℕ) (G : ℕ → X →L[𝕜] Y)
    (hG : ∀ k, ‖G k‖ ≤ 1) (f : ℕ ↪ ℕ) :
    (cZeroBlockInsert e G hG).comp (cZeroExtend f) =
      cZeroBlockInsert (f.trans e) (fun i => G (f i)) (fun i => hG (f i)) := by
  unfold cZeroBlockInsert
  rw [ContinuousLinearMap.comp_assoc, cZeroDiagonal_comp_extend,
    ← ContinuousLinearMap.comp_assoc, cZeroExtend_comp]

theorem cZeroBlockInsert_single (e : ℕ ↪ ℕ) (G : ℕ → X →L[𝕜] Y)
    (hG : ∀ k, ‖G k‖ ≤ 1) (n : ℕ) (x : X) :
    cZeroBlockInsert e G hG (cZeroSingle n x) = cZeroSingle (e n) (G n x) := by
  have hdiag : cZeroDiagonal G 1 zero_le_one hG (cZeroSingle n x) = cZeroSingle n (G n x) := by
    ext m
    by_cases hm : m = n
    · subst m; simp [cZeroSingle_apply]
    · simp [hm, cZeroSingle_apply]
  change cZeroExtend (𝕜 := 𝕜) e (cZeroDiagonal G 1 zero_le_one hG (cZeroSingle n x)) = _
  rw [hdiag, cZeroExtend_single]

theorem cZeroEntry_block_compression (T : CZeroSum Y →L[𝕜] CZeroSum Y)
    (e : ℕ ↪ ℕ) (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) (i j : ℕ) :
    cZeroEntry (((cZeroBlockRead e F hF).comp T).comp (cZeroBlockInsert e G hG)) i j =
      ((F i).comp (cZeroEntry T (e i) (e j))).comp (G j) := by
  ext x
  change F i (T (cZeroBlockInsert e G hG (cZeroSingle j x)) (e i)) =
    F i (T (cZeroSingle (e j) (G j x)) (e i))
  rw [cZeroBlockInsert_single]

theorem cZeroBlockCompression_tail_bound (T : CZeroSum Y →L[𝕜] CZeroSum Y)
    (e : ℕ ↪ ℕ) (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) (k : ℕ) :
    ‖((cZeroCoordinate k).comp (((cZeroBlockRead e F hF).comp T).comp (cZeroBlockInsert e G hG))).comp
      (cZeroExtend (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤
      ‖((F k).comp ((cZeroCoordinate (e k)).comp T)).comp (cZeroExtend (coordinateTail e k))‖ := by
  let s := coordinateTail (Function.Embedding.refl ℕ) k
  have heq : ((cZeroCoordinate k).comp
      (((cZeroBlockRead e F hF).comp T).comp (cZeroBlockInsert e G hG))).comp (cZeroExtend s) =
        (((F k).comp ((cZeroCoordinate (e k)).comp T)).comp (cZeroExtend (coordinateTail e k))).comp
          (cZeroDiagonal (fun i => G (s i)) 1 zero_le_one (fun i => hG (s i))) := by
    ext x
    have hx := DFunLike.congr_fun (cZeroBlockInsert_comp_extend e G hG s) x
    change cZeroBlockInsert e G hG (cZeroExtend (𝕜 := 𝕜) s x) =
      cZeroExtend (𝕜 := 𝕜) (coordinateTail e k)
        (cZeroDiagonal (fun i => G (s i)) 1 zero_le_one (fun i => hG (s i)) x) at hx
    change F k (T (cZeroBlockInsert e G hG (cZeroExtend (𝕜 := 𝕜) s x)) (e k)) = _
    rw [hx]
    rfl
  rw [heq]
  calc
    _ ≤ ‖((F k).comp ((cZeroCoordinate (e k)).comp T)).comp (cZeroExtend (coordinateTail e k))‖ *
        ‖cZeroDiagonal (fun i => G (s i)) 1 zero_le_one (fun i => hG (s i))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left (norm_cZeroDiagonal_le _ 1 zero_le_one _)
      (norm_nonneg (((F k).comp ((cZeroCoordinate (e k)).comp T)).comp
        (cZeroExtend (coordinateTail e k))))
    _ = _ := mul_one _

end ThesisCommon
