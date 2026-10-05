import PFP.SetMappingStatements
import ThesisCommon.Analysis.TwoSidedFreeSet

/-! Proof of Proposition 4.22 by the stated transfinite selection method. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u

theorem proposition_4_22 : Proposition_4_22.{u} := by
  intro κ hκ F _hmap hF
  have hΓ : Cardinal.aleph0 < Cardinal.mk κ.ord.toType := by
    simpa only [Cardinal.mk_ord_toType] using hκ
  obtain ⟨H, hcard, hfree⟩ := twoSided_countable_free_set F hF hΓ
  exact ⟨H, by simpa only [Cardinal.mk_ord_toType] using hcard, hfree⟩

end PFP
