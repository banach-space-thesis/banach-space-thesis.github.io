import Posets.ClosedIdealCountsTransport
import Posets.AlspachCounterexampleMetrizable
import ThesisCommon.Analysis.MilutinEquivalence
import Mathlib.SetTheory.Cardinal.Ordinal

/-! The fixed countable ordinal test space is complemented in C(K) for
every uncountable compact metric K. This transports actual ideal embeddings. -/
noncomputable section
open Set Topology TopologicalSpace ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

abbrev separableCountReferenceOrdinal : Ordinal.{0} :=
  Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))

theorem ordinalInterval_countable_of_card {α : Ordinal.{0}}
    (hc : α.card ≤ Cardinal.aleph0) : Countable (OrdinalInterval α) := by
  have hsc : (Order.succ α).card ≤ Cardinal.aleph0 := by
    rw [Ordinal.card_succ]
    calc
      α.card + 1 ≤ Cardinal.aleph0 + Cardinal.aleph0 :=
        add_le_add hc Cardinal.one_le_aleph0
      _ = Cardinal.aleph0 := Cardinal.aleph0_add_aleph0
  letI : Countable (Iio (Order.succ α)) := Cardinal.mk_le_aleph0_iff.mp (by
    rw [Ordinal.mk_Iio_ordinal]
    exact Cardinal.lift_le_aleph0.mpr hsc)
  exact Function.Injective.countable
    (f := fun x : OrdinalInterval α =>
      (⟨x.val, Order.lt_succ_of_le x.property.2⟩ : Iio (Order.succ α)))
    (fun x y h => Subtype.ext (congrArg (fun z : Iio (Order.succ α) => z.val) h))

theorem omega_power_card_le_aleph0 {α : Ordinal.{0}}
    (hc : α.card ≤ Cardinal.aleph0) :
    (Ordinal.omega0 ^ α).card ≤ Cardinal.aleph0 :=
  (Ordinal.card_opow_le_of_omega0_le_left le_rfl α).trans
    (max_le (by simp) hc)

theorem separableCountReference_countable : Countable (OrdinalInterval separableCountReferenceOrdinal) :=
  ordinalInterval_countable_of_card (omega_power_card_le_aleph0 (omega_power_card_le_aleph0
    ((Ordinal.card_le_card (Ordinal.nat_lt_omega0 2).le).trans (by simp))))

def nontrivialIdealEmbedding_uncountable_compactMetric (K : Type*)
    [MetricSpace K] [CompactSpace K] [Uncountable K] :
    NontrivialClosedIdeals 𝕜
      (OrdinalSpace 𝕜 separableCountReferenceOrdinal →L[𝕜] OrdinalSpace 𝕜 separableCountReferenceOrdinal) ↪
        NontrivialClosedIdeals 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜)) := by
  letI : Countable (OrdinalInterval separableCountReferenceOrdinal) := separableCountReference_countable
  letI : Nonempty (OrdinalInterval separableCountReferenceOrdinal) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  letI : MetrizableSpace (OrdinalInterval separableCountReferenceOrdinal) :=
    alspach_countable_compact_metrizable _
  letI : MetricSpace (OrdinalInterval separableCountReferenceOrdinal) := metrizableSpaceMetric _
  exact Classical.choice (by
    obtain ⟨e, he⟩ := milutin_exists_cantor_embedding K
    obtain ⟨P, J, _, _, hPJ⟩ := milutin_compactMetric_contractive_retract (𝕜 := 𝕜)
      (OrdinalInterval separableCountReferenceOrdinal) e he
    exact ⟨nontrivialIdealEmbeddingOfRetraction J P hPJ⟩)

end Posets
