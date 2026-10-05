import Posets.OrdinalLiftCompactCopy
import Posets.AlspachCounterexampleOrdinal
import Posets.SeparableMissingIdealCountEmbedding

/-! A continuous surjection from a compact metrizable space onto a countable
ordinal power admits a continuous section over a further closed copy. -/
noncomputable section
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Countable Y]

theorem ordinalLift_exists_ordinal_copy (f : X → Y) (hf : Continuous f)
    {A : Set X} (hA : IsCompact A) (himage : f '' A = univ)
    {α : Ordinal.{0}} (hα : α ≠ 0) (hc : α.card ≤ Cardinal.aleph0)
    (q : Y) (hD : ordinalDerived (univ : Set Y) α = {q}) :
    ∃ g : C(OrdinalInterval (ω ^ α), X),
      range g ⊆ A ∧ Function.Injective (f ∘ g) := by
  have hq : q ∈ f '' ordinalLiftIterate f A α := by
    rw [ordinalLiftIterate_image f hf hA, himage, hD]
    exact mem_singleton q
  obtain ⟨x, hx, hfx⟩ := hq
  obtain ⟨S, hSc, hSA, hSi, hxD⟩ := ordinalLift_exists_compact_injective_rank f hf A α hc hx
    isOpen_univ (mem_univ x)
  have hxS : x ∈ S := by
    simpa using ordinalDerived_antitone hSc.isClosed (Ordinal.zero_le α) hxD
  letI instCompactS : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  letI instCountableS : Countable S :=
    (show Function.Injective (fun z : S => f z.val) from
      fun a b he => Subtype.ext (hSi a.property b.property he)).countable
  let sx : S := ⟨x, hxS⟩
  have hcoe : IsClosedEmbedding (Subtype.val : S → X) := hSc.isClosed.isClosedEmbedding_subtypeVal
  have hdcoe := ordinalDerived_image_closedEmbedding hcoe univ α
  rw [image_univ, Subtype.range_coe] at hdcoe
  have hsx : sx ∈ ordinalDerived (univ : Set S) α := by
    rw [hdcoe] at hxD
    obtain ⟨y, hy, hyx⟩ := hxD
    have he : y = sx := Subtype.ext hyx
    exact he ▸ hy
  have hfS : IsClosedEmbedding (fun z : S => f z.val) :=
    (hf.comp continuous_subtype_val).isClosedEmbedding
      (fun a b he => Subtype.ext (hSi a.property b.property he))
  have hds : ordinalDerived (univ : Set S) α = {sx} := by
    apply subset_antisymm
    · intro y hy
      have hfy : f y.val ∈ ordinalDerived (univ : Set Y) α := by
        apply ordinalDerived_mono (subset_univ _) α
        rw [ordinalDerived_image_closedEmbedding hfS]
        exact mem_image_of_mem _ hy
      rw [hD] at hfy
      apply mem_singleton_iff.mpr
      exact Subtype.ext (hSi y.property hxS ((mem_singleton_iff.mp hfy).trans hfx.symm))
    · exact singleton_subset_iff.mpr hsx
  obtain ⟨e⟩ := alspach_countable_compact_singleton_homeomorph S sx α hα hds
  let g : C(OrdinalInterval (ω ^ α), X) :=
    ⟨fun t => (e.symm t).val, continuous_subtype_val.comp e.symm.continuous⟩
  refine ⟨g, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact (hSA (e.symm t).property).1
  · intro a b he
    apply e.symm.injective
    exact Subtype.ext (hSi (e.symm a).property (e.symm b).property he)

end Posets

namespace Posets
variable {X : Type*} [TopologicalSpace X] [MetrizableSpace X]

theorem ordinalLift_exists_continuous_section {α : Ordinal.{0}}
    (hα : α ≠ 0) (hc : α.card ≤ Cardinal.aleph0)
    (f : C(X, OrdinalInterval (ω ^ α))) {A : Set X}
    (hA : IsCompact A) (hsurj : f '' A = univ) :
    ∃ g : C(OrdinalInterval (ω ^ α), X),
      range g ⊆ A ∧ Function.Injective (f ∘ g) := by
  letI instMetricX : MetricSpace X := metrizableSpaceMetric X
  letI instCountableTarget : Countable (OrdinalInterval (ω ^ α)) :=
    ordinalInterval_countable_of_card (omega_power_card_le_aleph0 hc)
  letI instMetrizableTarget : MetrizableSpace (OrdinalInterval (ω ^ α)) :=
    alspach_countable_compact_metrizable _
  letI instMetricTarget : MetricSpace (OrdinalInterval (ω ^ α)) := metrizableSpaceMetric _
  exact ordinalLift_exists_ordinal_copy f f.continuous hA hsurj hα hc
    ⟨ω ^ α, Ordinal.zero_le _, le_rfl⟩ (alspach_ordinalInterval_power_ordinalDerived α hα)

end Posets

