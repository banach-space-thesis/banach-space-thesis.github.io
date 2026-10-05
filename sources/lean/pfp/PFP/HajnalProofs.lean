import PFP.SetMappingStatements
import ThesisCommon.Analysis.HajnalFreeSet

/-! The full Hajnal theorem in Proposition 4.21, including singular κ. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u

theorem proposition_4_21 : Proposition_4_21.{u} := by
  intro κ μ hκ hμ F _hmap hF
  obtain ⟨H, hcard, hfree⟩ := hajnal_free_set F μ
    (by simpa only [Cardinal.mk_ord_toType] using hκ)
    (by simpa only [Cardinal.mk_ord_toType] using hμ) hF
  exact ⟨H, by simpa only [Cardinal.mk_ord_toType] using hcard, hfree⟩

end PFP
