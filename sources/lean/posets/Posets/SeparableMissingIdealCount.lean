import Posets.SeparableMissingIdealCountCases
import Posets.SeparableMetrizable

/-! The uniform missing value among two and three in Proposition 3.4.
The only input is its first clause: four actual nontrivial closed ideals
in the fixed large ordinal operator algebra. -/
noncomputable section
open Set Topology TopologicalSpace ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem exists_missing_two_or_three (A : Type*) :
    ∃ n : ℕ, (n = 2 ∨ n = 3) ∧ ¬ Nonempty (A ≃ Fin n) := by
  classical
  by_cases htwo : Nonempty (A ≃ Fin 2)
  · refine ⟨3, Or.inr rfl, ?_⟩
    rintro ⟨ethree⟩
    obtain ⟨etwo⟩ := htwo
    have hh := Fintype.card_congr (etwo.symm.trans ethree)
    norm_num at hh
  · exact ⟨2, Or.inl rfl, htwo⟩

theorem missingSeparableIdealCount_of_four_ordinalIdeals
    (h4 : Nonempty (Fin 4 ↪ OrdinalReferenceNontrivialIdeals 𝕜)) :
    MissingSeparableIdealCount 𝕜 := by
  obtain ⟨n, hn, hgap⟩ := exists_missing_two_or_three (OrdinalMiddleNontrivialIdeals 𝕜)
  refine ⟨n, hn, ?_⟩
  intro K _ _ _ hsep
  letI := hsep
  letI : MetrizableSpace K := metrizable_of_separable_continuousMap (𝕜 := 𝕜) K
  letI : MetricSpace K := metrizableSpaceMetric K
  exact compactMetric_not_equiv_fin_of_middle_gap h4 (by omega) (by omega) hgap K

end Posets
