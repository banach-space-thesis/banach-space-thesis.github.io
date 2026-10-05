import ThesisCommon.Analysis.UnitCharge

/-! The zero charge and point-mass charges, with their finite variation bounds. -/
noncomputable section
open Set
namespace ThesisCommon

instance {α : Type*} : Zero (UnitCharge α) where
  zero := {
    toFun := fun _ => 0
    map_empty := rfl
    map_union := by intros; simp
    variation_le := by intros; simp }

@[simp] theorem UnitCharge.zero_apply {α : Type*} (A : Set α) : (0 : UnitCharge α) A = 0 := rfl

instance {α : Type*} : Inhabited (UnitCharge α) := ⟨0⟩

end ThesisCommon
