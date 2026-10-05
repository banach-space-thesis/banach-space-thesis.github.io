import ThesisCommon.Analysis.OrdinalBakerNormal
import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Topology.Constructions.SumProd
import Mathlib.SetTheory.Ordinal.Principal

/-! Explicit topological sums of compact ordinal intervals. The successor
between the two blocks makes both summands clopen. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

/-- Concatenating two compact ordinal intervals with a successor gap gives
their topological disjoint union, for arbitrary ordinal endpoints. -/
def ordinalIntervalSumHomeomorph (α β : Ordinal.{u}) :
    (OrdinalInterval α ⊕ OrdinalInterval β) ≃ₜ OrdinalInterval (α + 1 + β) := by
  let f : OrdinalInterval α ⊕ OrdinalInterval β → OrdinalInterval (α + 1 + β) :=
    Sum.elim
      (fun x => ⟨x.val, bot_le, x.property.2.trans
        ((Ordinal.le_add_right α 1).trans (Ordinal.le_add_right (α + 1) β))⟩)
      (fun y => ⟨α + 1 + y.val, bot_le, add_le_add_left y.property.2 (α + 1)⟩)
  have hcont : Continuous f := by
    apply Continuous.sumElim
    · exact continuous_subtype_val.subtype_mk _
    · exact ((Ordinal.isNormal_add_right (α + 1)).continuous.comp
        continuous_subtype_val).subtype_mk _
  have hsep (x : OrdinalInterval α) (y : OrdinalInterval β) :
      x.val < α + 1 + y.val := by
    have h : x.val < α + 1 := by
      simpa only [Ordinal.add_one_eq_succ] using x.property.2.trans_lt (lt_succ α)
    exact h.trans_le (Ordinal.le_add_right (α + 1) y.val)
  have hinj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext
          (congrArg (fun z : OrdinalInterval (α + 1 + β) => z.val) hxy))
      | inr y => exact False.elim ((ne_of_lt (hsep x y))
          (congrArg (fun z : OrdinalInterval (α + 1 + β) => z.val) hxy))
    | inr x =>
      cases y with
      | inl y => exact False.elim ((ne_of_lt (hsep y x))
          (congrArg (fun z : OrdinalInterval (α + 1 + β) => z.val) hxy).symm)
      | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact add_left_cancel (congrArg (fun z : OrdinalInterval (α + 1 + β) => z.val) hxy)
  have hsurj : Function.Surjective f := by
    intro z
    by_cases hz : z.val ≤ α
    · exact ⟨Sum.inl ⟨z.val, bot_le, hz⟩, Subtype.ext rfl⟩
    · have hα : α + 1 ≤ z.val := by
        simpa only [Ordinal.add_one_eq_succ] using succ_le_iff.mpr (lt_of_not_ge hz)
      refine ⟨Sum.inr ⟨z.val - (α + 1), bot_le, Ordinal.sub_le.mpr z.property.2⟩, ?_⟩
      exact Subtype.ext (Ordinal.add_sub_cancel_of_le hα)
  exact (show Continuous (Equiv.ofBijective f ⟨hinj, hsurj⟩) from hcont).homeoOfEquivCompactToT2

end ThesisCommon
