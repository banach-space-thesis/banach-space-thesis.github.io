import Posets.AlspachCounterexamplePointed

/-! Transport of explicit probability forests along bijections of their
point and row sets. This connects the algebraic sum models with the compact
Hausdorff graft models without altering their rows or estimates. -/

noncomputable section
namespace Posets
namespace AlspachPointedRows
variable {𝕜 K I L J : Type*} [RCLike 𝕜]

def reindex (F : AlspachPointedRows 𝕜 K I) (e : K ≃ L) (d : I ≃ J) :
    AlspachPointedRows 𝕜 L J where
  point := e F.point
  index := d F.index
  parent j := (F.parent (d.symm j)).map d
  depth j := F.depth (d.symm j)
  parent_lt i j hij := by
    cases hp : F.parent (d.symm i) with
    | none => simp [hp] at hij
    | some a =>
        simp only [hp, Option.map_some, Option.some.injEq] at hij
        subst j
        simpa only [d.symm_apply_apply] using F.parent_lt (d.symm i) a hp
  parent_none i := by simp [F.parent_none, Equiv.symm_apply_eq]
  depth_root := by simpa only [d.symm_apply_apply] using F.depth_root
  privateRow j := (F.privateRow (d.symm j)).map e
  row j := (F.row (d.symm j)).map e
  owner x := d (F.owner (e.symm x))
  owner_root x := by simp [F.owner_root, Equiv.symm_apply_eq]
  owner_private i x hx := by
    obtain ⟨k, hk, rfl⟩ := (AlspachProbability.mem_support_map _ _ _).mp hx
    simp only [e.symm_apply_apply, F.owner_private _ _ hk, d.apply_symm_apply]
  private_root := by simp only [d.symm_apply_apply, F.private_root, AlspachProbability.map]
  row_root := by simp only [d.symm_apply_apply, F.row_root, AlspachProbability.map]
  child_row i j hij := by
    cases hp : F.parent (d.symm i) with
    | none => simp [hp] at hij
    | some a =>
        simp only [hp, Option.map_some, Option.some.injEq] at hij
        subst j
        have he := congrArg (AlspachProbability.mapLinear (𝕜 := 𝕜) e)
          (F.child_row (d.symm i) a hp)
        simpa only [map_smul, map_add, AlspachProbability.mapLinear_vector,
          d.symm_apply_apply] using he

end AlspachPointedRows
end Posets
