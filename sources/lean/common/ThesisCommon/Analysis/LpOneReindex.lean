import ThesisCommon.Analysis.LpOneComap

/-! Coordinate relabelling is an actual linear isometry of real ell-one spaces. -/
noncomputable section
namespace ThesisCommon

def lpOneReindex {ι κ : Type*} (e : ι ≃ κ) :
    lp (fun _ : κ => ℝ) 1 ≃ₗᵢ[ℝ] lp (fun _ : ι => ℝ) 1 where
  toFun := lpOneComap e.toEmbedding
  invFun := lpOneComap e.symm.toEmbedding
  left_inv f := by apply lp.ext; funext i; simp
  right_inv f := by apply lp.ext; funext i; simp
  map_add' _ _ := by apply lp.ext; rfl
  map_smul' _ _ := by apply lp.ext; rfl
  norm_map' f := by
    apply le_antisymm (lpOneComap_norm_le _ _)
    have h := lpOneComap_norm_le e.symm.toEmbedding (lpOneComap e.toEmbedding f)
    have heq : lpOneComap e.symm.toEmbedding (lpOneComap e.toEmbedding f) = f := by
      apply lp.ext
      funext i
      simp
    rwa [heq] at h

@[simp] theorem lpOneReindex_apply {ι κ : Type*} (e : ι ≃ κ)
    (f : lp (fun _ : κ => ℝ) 1) (i : ι) : lpOneReindex e f i = f (e i) := rfl

end ThesisCommon
