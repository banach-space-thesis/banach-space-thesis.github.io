import Posets.AlspachCounterexampleBase
import Posets.AlspachCounterexampleProbabilityCalculus

/-! Pointed finite-support probability families. This records the concrete
data preserved by Alspach's successor and limit constructions; it contains
neither a surjectivity assumption nor a lower-estimate assumption. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable (𝕜 K I : Type*) [RCLike 𝕜]

structure AlspachPointedRows where
  point : K
  index : I
  parent : I → Option I
  depth : I → ℕ
  parent_lt : ∀ i j, parent i = some j → depth j < depth i
  parent_none : ∀ i, parent i = none ↔ i = index
  depth_root : depth index = 0
  privateRow : I → AlspachProbability K
  row : I → AlspachProbability K
  owner : K → I
  owner_root : ∀ k, owner k = index ↔ k = point
  owner_private : ∀ i k, k ∈ (privateRow i).support → owner k = i
  private_root : privateRow index = .point point
  row_root : row index = .point point
  child_row : ∀ i j, parent i = some j →
    (row i).vector (𝕜 := 𝕜) = (1 / 2 : 𝕜) • ((privateRow i).vector + (row j).vector)

namespace AlspachPointedRows
variable {𝕜 K I : Type*} [RCLike 𝕜] (F : AlspachPointedRows 𝕜 K I)

def forest : AlspachForestRows 𝕜 I (lp (fun _ : K => 𝕜) 1) where
  parent := F.parent
  depth := F.depth
  parent_lt := F.parent_lt
  privateRow i := (F.privateRow i).vector
  row i := (F.row i).vector
  read := alspachOwnerRead (fun k => some (F.owner k))
  read_norm_le := alspachOwnerRead_norm_le _
  read_private i := alspachOwnerRead_probability _ _ _ (fun k hk =>
    congrArg some (F.owner_private i k hk))
  root_row i hi := by
    obtain rfl := (F.parent_none i).mp hi
    rw [F.row_root, F.private_root]
  child_row := F.child_row
  row_norm_le i := (F.row i).vector_norm_le

theorem depth_pos {i : I} (hi : i ≠ F.index) : 0 < F.depth i := by
  cases hp : F.parent i with
  | none => exact (hi ((F.parent_none i).mp hp)).elim
  | some j => exact (Nat.zero_le _).trans_lt (F.parent_lt i j hp)

theorem point_not_mem_private {i : I} (hi : i ≠ F.index) :
    F.point ∉ (F.privateRow i).support := by
  intro h
  have he := F.owner_private i F.point h
  have hr := (F.owner_root F.point).mpr rfl
  exact hi (he.symm.trans hr)

def base (p : K) : AlspachPointedRows 𝕜 K K where
  point := p
  index := p
  parent x := if x = p then none else some p
  depth x := if x = p then 0 else 1
  parent_lt := (alspachBaseForest (𝕜 := 𝕜) p).parent_lt
  parent_none x := by simp
  depth_root := by simp
  privateRow x := .point x
  row := alspachBaseRow p
  owner := id
  owner_root _ := Iff.rfl
  owner_private i k hk := by simpa [AlspachProbability.support] using hk
  private_root := rfl
  row_root := by simp [alspachBaseRow]
  child_row := (alspachBaseForest (𝕜 := 𝕜) p).child_row

end AlspachPointedRows
end Posets

