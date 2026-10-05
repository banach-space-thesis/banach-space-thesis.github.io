import ThesisCommon.Analysis.CountableOrdinalContinuous
import ThesisCommon.Analysis.ContinuousMapPullback

/-! Universe-independent countable ordinal intervals have actual small
ordinal models. The transport is an order homeomorphism induced by ordinal
lifting, not a cardinality-only replacement of the compact topology. -/
noncomputable section
open Set
namespace ThesisCommon
universe u v

def ordinalIntervalLiftOrderIso (α : Ordinal.{u}) :
    OrdinalInterval α ≃o OrdinalInterval (Ordinal.lift.{v} α) := by
  let f : OrdinalInterval α ↪o OrdinalInterval (Ordinal.lift.{v} α) :=
    { toFun := fun x => ⟨Ordinal.lift x.val, Ordinal.zero_le _, Ordinal.lift_le.mpr x.property.2⟩
      inj' := fun x y h => Subtype.ext (Ordinal.lift_inj.mp (congrArg Subtype.val h))
      map_rel_iff' := by intro x y; exact Ordinal.lift_le }
  apply StrictMono.orderIsoOfSurjective f f.strictMono
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, hxy⟩ := Ordinal.le_lift_iff.mp hx.2
  exact ⟨⟨y, Ordinal.zero_le _, hy⟩, Subtype.ext hxy⟩

def ordinalIntervalLiftHomeomorph (α : Ordinal.{u}) :
    OrdinalInterval α ≃ₜ OrdinalInterval (Ordinal.lift.{v} α) :=
  (ordinalIntervalLiftOrderIso α).toHomeomorph

theorem exists_countableOrdinal_small_model {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) :
    ∃ β : Ordinal.{0}, β.card ≤ Cardinal.aleph0 ∧
      Nonempty (OrdinalInterval α ≃ₜ OrdinalInterval β) := by
  have hc : α.card ≤ Cardinal.lift.{u, 0} Cardinal.aleph0 := by
    simpa only [← Cardinal.succ_aleph0, Order.lt_succ_iff, Cardinal.lift_aleph0]
      using (Cardinal.lt_ord.mp hα)
  obtain ⟨β, rfl⟩ := Ordinal.mem_range_lift_of_card_le hc
  refine ⟨β, ?_, ⟨(ordinalIntervalLiftHomeomorph.{0, u} β).symm⟩⟩
  rw [← Ordinal.lift_card, Cardinal.lift_le] at hc
  exact hc

theorem exists_countableOrdinal_small_infinite_model {α : Ordinal.{u}}
    (hα : α < (Cardinal.aleph 1).ord) (hαinf : Ordinal.omega0 ≤ α) :
    ∃ β : Ordinal.{0}, β.card ≤ Cardinal.aleph0 ∧ Ordinal.omega0 ≤ β ∧
      Nonempty (OrdinalInterval α ≃ₜ OrdinalInterval β) := by
  have hc : α.card ≤ Cardinal.lift.{u, 0} Cardinal.aleph0 := by
    simpa only [← Cardinal.succ_aleph0, Order.lt_succ_iff, Cardinal.lift_aleph0]
      using (Cardinal.lt_ord.mp hα)
  obtain ⟨β, rfl⟩ := Ordinal.mem_range_lift_of_card_le hc
  refine ⟨β, ?_, ?_, ⟨(ordinalIntervalLiftHomeomorph.{0, u} β).symm⟩⟩
  · rw [← Ordinal.lift_card, Cardinal.lift_le] at hc
    exact hc
  · exact Ordinal.lift_le.mp (by simpa using hαinf)

end ThesisCommon
