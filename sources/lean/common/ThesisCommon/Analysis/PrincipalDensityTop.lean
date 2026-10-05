import ThesisCommon.Analysis.BooleanDensityHomogeneity

/-! The principal ideal below top has the actual density of the whole space. -/
noncomputable section
open Set
namespace ThesisCommon

theorem principalDensity_top {B : Type*} [SemilatticeInf B] [OrderBot B]
    [OrderTop B] [TopologicalSpace B] [ContinuousInf B] :
    principalDensity (⊤ : B) = topologicalDensity B := by
  change topologicalDensity (Iic (⊤ : B)) = topologicalDensity B
  apply le_antisymm
  · apply topologicalDensity_le_of_continuous_surjective
      (f := fun x : B => (⟨x, le_top⟩ : Iic (⊤ : B)))
    · exact continuous_id.subtype_mk _
    · intro x
      exact ⟨x.val, Subtype.ext rfl⟩
  · apply topologicalDensity_le_of_continuous_surjective
      (f := fun x : Iic (⊤ : B) => x.val) continuous_subtype_val
    intro x
    exact ⟨⟨x, le_top⟩, rfl⟩

end ThesisCommon
