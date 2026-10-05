import Posets.SeparableMissingIdealCountEmbedding
import Posets.OrdinalMiddleClassification
import Posets.SeparableIdealCorollary

/-! The finite, low ordinal, middle ordinal, high ordinal and uncountable
compact cases for the uniform missing ideal count. -/
noncomputable section
open Set Topology ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

abbrev OrdinalMiddleNontrivialIdeals (𝕜 : Type) [RCLike 𝕜] :=
  NontrivialClosedIdeals 𝕜
    (OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) →L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})))

abbrev OrdinalReferenceNontrivialIdeals (𝕜 : Type) [RCLike 𝕜] :=
  NontrivialClosedIdeals 𝕜
    (OrdinalSpace 𝕜 separableCountReferenceOrdinal →L[𝕜]
      OrdinalSpace 𝕜 separableCountReferenceOrdinal)

theorem ordinal_not_equiv_fin_of_middle_gap
    (h4 : Nonempty (Fin 4 ↪ OrdinalReferenceNontrivialIdeals 𝕜))
    {n : ℕ} (hnlo : 1 < n) (hnhi : n < 4)
    (hgap : ¬ Nonempty (OrdinalMiddleNontrivialIdeals 𝕜 ≃ Fin n))
    (α : Ordinal.{0}) (hα : Ordinal.omega0 ≤ α) :
    ¬ Nonempty (NontrivialClosedIdeals 𝕜 (OrdinalSpace 𝕜 α →L[𝕜] OrdinalSpace 𝕜 α) ≃ Fin n) := by
  rintro ⟨e⟩
  by_cases hlo : α < Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})
  · obtain ⟨f⟩ := ordinalBelowOmegaOmega_nontrivialIdealEquivFinOne (𝕜 := 𝕜) α hα hlo
    have hh := Fintype.card_congr (f.symm.trans e)
    simp only [Fintype.card_fin] at hh
    omega
  · by_cases hhi : α < separableCountReferenceOrdinal
    · obtain ⟨f⟩ := nonempty_nontrivialIdealEquiv (ordinalMiddleEquiv (𝕜 := 𝕜) α (le_of_not_gt hlo) hhi)
      exact hgap ⟨f.symm.trans e⟩
    · obtain ⟨j⟩ := h4
      exact not_equiv_fin_of_fin_embedding hnhi
        (j.trans (ordinalNontrivialIdealEmbedding (𝕜 := 𝕜) (le_of_not_gt hhi))) ⟨e⟩

theorem compactMetric_not_equiv_fin_of_middle_gap
    (h4 : Nonempty (Fin 4 ↪ OrdinalReferenceNontrivialIdeals 𝕜))
    {n : ℕ} (hnlo : 1 < n) (hnhi : n < 4)
    (hgap : ¬ Nonempty (OrdinalMiddleNontrivialIdeals 𝕜 ≃ Fin n))
    (K : Type) [MetricSpace K] [CompactSpace K] :
    ¬ Nonempty (NontrivialClosedIdeals 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜)) ≃ Fin n) := by
  classical
  cases finite_or_infinite K with
  | inl hfinite =>
      letI := hfinite
      letI := isEmpty_nontrivialIdeals_finiteCompact (𝕜 := 𝕜) K
      rintro ⟨e⟩
      exact isEmptyElim (e.symm ⟨0, by omega⟩)
  | inr hinfinite =>
      letI := hinfinite
      by_cases hc : Countable K
      · letI := hc
        obtain ⟨α, hα, ⟨f⟩⟩ := countableCompact_infinite_ordinalModel K
        obtain ⟨g⟩ := nonempty_nontrivialIdealEquiv (continuousMapHomeomorphEquiv (𝕜 := 𝕜) f)
        rintro ⟨e⟩
        exact ordinal_not_equiv_fin_of_middle_gap h4 hnlo hnhi hgap α hα ⟨g.symm.trans e⟩
      · letI : Uncountable K := ⟨hc⟩
        obtain ⟨j⟩ := h4
        exact not_equiv_fin_of_fin_embedding hnhi
          (j.trans (nontrivialIdealEmbedding_uncountable_compactMetric (𝕜 := 𝕜) K))

end Posets
