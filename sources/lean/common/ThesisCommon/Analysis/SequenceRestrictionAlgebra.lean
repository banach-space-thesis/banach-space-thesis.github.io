import ThesisCommon.Analysis.SequenceEmbeddingAlgebra

/-! Output-coordinate restriction composition and norm monotonicity.
These are the dual coordinate-algebra counterparts of zero-insertion facts.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {ι κ ν : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lpRestrict_comp (e : ι ↪ κ) (f : κ ↪ ν) :
    (lpRestrict (𝕜 := 𝕜) (X := X) p e).comp (lpRestrict p f) =
      lpRestrict p (e.trans f) := by
  ext x i
  rfl

theorem norm_lpRestrict_comp_le (T : Y →L[𝕜] lp (fun _ : κ => X) p) (e : ι ↪ κ) :
    ‖(lpRestrict p e).comp T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖lpRestrict (𝕜 := 𝕜) (X := X) p e‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_lpRestrict_le e) (norm_nonneg T)
    _ = _ := one_mul _

theorem norm_lpRestrict_comp_le_of_range_subset
    (T : Y →L[𝕜] lp (fun _ : ν => X) p) (e : κ ↪ ν) (f : ι ↪ ν)
    (h : Set.range f ⊆ Set.range e) :
    ‖(lpRestrict p f).comp T‖ ≤ ‖(lpRestrict p e).comp T‖ := by
  obtain ⟨g, rfl⟩ := exists_embedding_factor e f h
  rw [← lpRestrict_comp, ContinuousLinearMap.comp_assoc]
  exact norm_lpRestrict_comp_le _ g

end ThesisCommon
