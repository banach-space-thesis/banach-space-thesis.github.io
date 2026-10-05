import Posets.AlspachCounterexampleMetrizable
import Posets.SeparableIdealClassification
import ThesisCommon.Analysis.OrdinalBakerSingleton
import Mathlib.Topology.Instances.Shrink

/-! The actual ordinal model of a countable compact Hausdorff space whose
last nonempty Cantor–Bendixson derivative is a singleton. The intermediate
shrinking only changes universes, not the topology. -/

noncomputable section
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets

theorem alspach_countable_compact_ordinalModel (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [Countable K] [Nonempty K] :
    ∃ α : Ordinal.{0}, Nonempty (K ≃ₜ OrdinalInterval α) := by
  let e : K ≃ₜ Shrink.{0} K := Shrink.homeomorph.{0} K
  letI : CompactSpace (Shrink.{0} K) := e.compactSpace
  letI : T2Space (Shrink.{0} K) := e.t2Space
  letI : Countable (Shrink.{0} K) := e.toEquiv.countable_iff.mp inferInstance
  letI : Nonempty (Shrink.{0} K) := e.symm.toEquiv.nonempty
  letI : MetrizableSpace (Shrink.{0} K) := alspach_countable_compact_metrizable _
  letI : MetricSpace (Shrink.{0} K) := metrizableSpaceMetric (Shrink.{0} K)
  obtain ⟨α, ⟨h⟩⟩ := countableCompact_hasOrdinalCompactModel (Shrink.{0} K)
  exact ⟨α, ⟨e.trans h⟩⟩

theorem alspach_countable_compact_singleton_homeomorph
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Countable K]
    (p : K) (η : Ordinal.{0}) (hη : η ≠ 0)
    (hD : ordinalDerived (univ : Set K) η = {p}) :
    Nonempty (K ≃ₜ OrdinalInterval (ω ^ η)) := by
  letI : Nonempty K := ⟨p⟩
  obtain ⟨α, ⟨e⟩⟩ := alspach_countable_compact_ordinalModel K
  let f : K → Ordinal.{0} := fun x => (e x).val
  have hf : IsClosedEmbedding f :=
    (isClosed_Icc : IsClosed (Icc (0 : Ordinal.{0}) α)).isClosedEmbedding_subtypeVal.comp
      e.isClosedEmbedding
  have hr : f '' univ = Icc (0 : Ordinal.{0}) α := by
    rw [← image_image]
    simp only [image_univ, e.surjective.range_eq, Subtype.range_coe]
  have hd := ordinalDerived_image_closedEmbedding hf univ η
  rw [hr, hD, image_singleton] at hd
  obtain ⟨h⟩ := ordinal_compact_singleton_derivative_homeomorph isCompact_Icc hη hd
  exact ⟨e.trans h.symm⟩

end Posets
