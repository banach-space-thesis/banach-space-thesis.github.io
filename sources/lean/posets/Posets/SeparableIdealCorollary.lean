import Posets.SeparableIdealClassification
import Posets.SeparableIdealCases
import ThesisCommon.Analysis.OrdinalBakerOmega

/-! The topological and Milutin reductions for Corollary 3.3. -/
noncomputable section
open Set ThesisCommon
namespace Posets

theorem omega_le_of_infinite_ordinalModel {K : Type*} [TopologicalSpace K] [Infinite K]
    {α : Ordinal.{0}} (e : K ≃ₜ OrdinalInterval α) : Ordinal.omega0 ≤ α := by
  by_contra h
  have hf : (Set.Icc (0 : Ordinal.{0}) α).Finite :=
    (ordinal_finite_Iic_of_lt_omega (lt_of_not_ge h)).subset Set.Icc_subset_Iic_self
  letI : Finite (OrdinalInterval α) := hf.to_subtype
  haveI : Finite K := Finite.of_equiv (OrdinalInterval α) e.toEquiv.symm
  exact not_finite K

theorem countableCompact_infinite_ordinalModel
    (K : Type) [MetricSpace K] [CompactSpace K] [Countable K] [Infinite K] :
    ∃ α : Ordinal.{0}, Ordinal.omega0 ≤ α ∧ Nonempty (K ≃ₜ OrdinalInterval α) := by
  obtain ⟨α, ⟨e⟩⟩ := countableCompact_hasOrdinalCompactModel K
  exact ⟨α, omega_le_of_infinite_ordinalModel e, ⟨e⟩⟩

/-- The printed Section 3 corollary follows from Proposition 3.1, with the
nonempty compact-space hypothesis made explicit in its formal target. -/
theorem corollary_3_3_of_proposition_3_1 {𝕜 : Type} [RCLike 𝕜]
    (hord : ∀ α : Ordinal.{0}, Proposition_3_1 𝕜 α) : Corollary_3_3 𝕜 := by
  apply corollary_3_3_of_countablyInfinite
  intro K _ _ _ _
  exact countable_compact_uniqueMaximalClosedIdeal_of_ordinalModel hord K
    (countableCompact_infinite_ordinalModel K)

end Posets
