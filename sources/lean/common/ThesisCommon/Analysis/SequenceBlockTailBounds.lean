import ThesisCommon.Analysis.SequenceBlockAlgebra
import ThesisCommon.Analysis.SequenceRestrictionAlgebra

/-! Tail bounds survive increasing block compressions. The proof uses
whole-tail operator norms and containment of the selected future coordinates.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem norm_comp_left_contraction (A : Y →L[𝕜] Z) (hA : ‖A‖ ≤ 1) (T : X →L[𝕜] Y) :
    ‖A.comp T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖A‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg T)
    _ = _ := one_mul _

theorem norm_comp_right_contraction (T : Y →L[𝕜] Z) (B : X →L[𝕜] Y) (hB : ‖B‖ ≤ 1) :
    ‖T.comp B‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖T‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hB (norm_nonneg T)
    _ = _ := mul_one _

theorem coordinateTail_range_subset (e : ℕ ↪ ℕ) (he : StrictMono e) (k : ℕ) :
    Set.range (coordinateTail e k) ⊆
      Set.range (coordinateTail (Function.Embedding.refl ℕ) (e k)) := by
  rintro _ ⟨j, rfl⟩
  have hgt := he (show k < k + 1 + j by omega)
  refine ⟨e (k+1+j) - (e k+1), ?_⟩
  change e k + 1 + (e (k+1+j) - (e k+1)) = e (k+1+j)
  omega

theorem lpBlockCompression_preserves_tail_bound {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (T : lp (fun _ : ℕ => Y) q →L[𝕜] lp (fun _ : ℕ => Y) q)
    (e : ℕ ↪ ℕ) (he : StrictMono e)
    (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) {b : ℝ}
    (hT : ∀ k, ‖((lpCoordinate q k).comp T).comp
      (lpExtend q (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ b) (k : ℕ) :
    ‖((lpCoordinate q k).comp (((lpBlockRead q e F hF).comp T).comp (lpBlockInsert q e G hG))).comp
      (lpExtend q (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ b := by
  apply (lpBlockCompression_tail_bound q T e F G hF hG k).trans
  rw [ContinuousLinearMap.comp_assoc]
  apply (norm_comp_left_contraction (F k) (hF k) _).trans
  exact (norm_comp_lpExtend_le_of_range_subset ((lpCoordinate q (e k)).comp T)
    (coordinateTail (Function.Embedding.refl ℕ) (e k)) (coordinateTail e k)
      (coordinateTail_range_subset e he k)).trans (hT (e k))

theorem cZeroBlockCompression_preserves_tail_bound (T : CZeroSum Y →L[𝕜] CZeroSum Y)
    (e : ℕ ↪ ℕ) (he : StrictMono e)
    (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG) {b : ℝ}
    (hT : ∀ k, ‖((cZeroCoordinate k).comp T).comp
      (cZeroExtend (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ b) (k : ℕ) :
    ‖((cZeroCoordinate k).comp (((cZeroBlockRead e F hF).comp T).comp (cZeroBlockInsert e G hG))).comp
      (cZeroExtend (coordinateTail (Function.Embedding.refl ℕ) k))‖ ≤ b := by
  apply (cZeroBlockCompression_tail_bound T e F G hF hG k).trans
  rw [ContinuousLinearMap.comp_assoc]
  apply (norm_comp_left_contraction (F k) (hF k) _).trans
  exact (norm_comp_cZeroExtend_le_of_range_subset ((cZeroCoordinate (e k)).comp T)
    (coordinateTail (Function.Embedding.refl ℕ) (e k)) (coordinateTail e k)
      (coordinateTail_range_subset e he k)).trans (hT (e k))

end ThesisCommon
