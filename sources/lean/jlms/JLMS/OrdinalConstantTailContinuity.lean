import JLMS.OrdinalTailConstancy

/-! # Continuity at an ordinal endpoint from a constant final tail -/

namespace JLMS
open Filter Topology
universe u

theorem continuousAt_of_ordinal_constant_tail {M : Type*} [TopologicalSpace M]
    {α β : Ordinal.{u}} (hβ : β < α) (f : OrdinalInterval α → M)
    (hf : ∀ x : OrdinalInterval α, β < x.val →
      f x = f ⟨α, Ordinal.zero_le _, le_rfl⟩) :
    ContinuousAt f ⟨α, Ordinal.zero_le _, le_rfl⟩ := by
  apply continuousAt_const.congr_of_eventuallyEq
  have hU : {x : OrdinalInterval α | β < x.val} ∈
      𝓝 (⟨α, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval α) := by
    have ho : IsOpen {x : OrdinalInterval α | β < x.val} :=
      isOpen_Ioi.preimage (continuous_subtype_val :
        Continuous (Subtype.val : OrdinalInterval α → Ordinal.{u}))
    exact ho.mem_nhds hβ
  filter_upwards [hU] with x hx
  exact hf x hx

end JLMS
