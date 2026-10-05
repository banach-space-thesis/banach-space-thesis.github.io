import Posets.AlspachCounterexampleNonfactorization
import Posets.OrdinalLiftRetraction
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Alspach's stronger nonpreservation property: no operator inserting a
copy of the domain can make the surjection bounded below on that copy. -/

noncomputable section
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem alspachOrdinalOperator_doesNotPreserveCopy :
    ¬ ∃ J : OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) →L[𝕜]
        OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))),
      ∃ c : ℝ, 0 < c ∧ ∀ f, c * ‖f‖ ≤ ‖alspachOrdinalOperator (J f)‖ := by
  letI : Countable AlspachOrdinalCompact := separableCountReference_countable
  letI : MetrizableSpace AlspachOrdinalCompact := alspach_countable_compact_metrizable _
  letI : MetricSpace AlspachOrdinalCompact := metrizableSpaceMetric _
  letI : SeparableSpace (OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0})))) := inferInstance
  intro ⟨J, c, hc, hlower⟩
  have hα : (ω : Ordinal.{0}) ^ (2 : Ordinal) ≠ 0 :=
    Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero
  have hcount : ((ω : Ordinal.{0}) ^ (2 : Ordinal)).card ≤ Cardinal.aleph0 :=
    omega_power_card_le_aleph0 ((Ordinal.card_le_card (Ordinal.nat_lt_omega0 2).le).trans (by simp))
  obtain ⟨S, R, hfactor, _, _⟩ := exists_ordinal_embedding_identity_factors hα hcount
    (alspachOrdinalOperator.comp J) hc hlower
  apply alspachOrdinalOperator_doesNotFactorIdentity (𝕜 := 𝕜)
  exact ⟨J.comp S, R, by simpa only [ContinuousLinearMap.comp_assoc] using hfactor⟩

end Posets
