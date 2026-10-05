import ThesisCommon.Analysis.PrincipalDensityTop
import ThesisCommon.Analysis.OrderIsoDensity

/-! Passing to a principal ideal preserves the intrinsic density of all
its smaller principal ideals and preserves homogeneity at the top. -/
noncomputable section
open Set
namespace ThesisCommon
variable {B : Type*} [Lattice B] [OrderBot B] [TopologicalSpace B] [ContinuousInf B]

def principalIdealNestedHomeomorph (a : B) (b : Iic a) : Iic b ≃ₜ Iic b.val where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.trans b.property⟩, x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem principalDensity_Iic (a : B) (b : Iic a) :
    principalDensity b = principalDensity b.val :=
  topologicalDensity_eq_of_homeomorph (principalIdealNestedHomeomorph a b)

theorem isDensityHomogeneous_Iic_top_iff (a : B) :
    IsDensityHomogeneous (⊤ : Iic a) ↔ IsDensityHomogeneous a := by
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨fun haz => ha (Subtype.ext haz), ?_⟩
    intro b hb hba
    have hb' : (⟨b, hba⟩ : Iic a) ≠ ⊥ := fun h => hb (congrArg Subtype.val h)
    have h' := h ⟨b, hba⟩ hb' le_top
    simpa only [principalDensity_Iic] using h'
  · rintro ⟨ha, h⟩
    refine ⟨fun haz => ha (congrArg Subtype.val haz), ?_⟩
    intro b hb _
    have hb' : b.val ≠ ⊥ := fun h => hb (Subtype.ext h)
    simpa only [principalDensity_Iic] using h b.val hb' b.property

end ThesisCommon
