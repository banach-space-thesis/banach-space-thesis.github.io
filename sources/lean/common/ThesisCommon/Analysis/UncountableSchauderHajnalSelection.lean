import ThesisCommon.Analysis.CountableRelationFreeSet
import ThesisCommon.Analysis.UncountableSchauderDiagonalSelection

/-! One-sided Hajnal selection on actual coordinate entries of the genuine
norm-series space. The local either-or hypothesis is handled by a full-sized
monochromatic restriction. Countable total duals supply incoming support via
the checked operator-support theorem of Lemma 4.18. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
namespace UncountableSchauderSum
variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {b : NormalizedSchauderFamily 𝕜 Γ E} {hb : b.IsOneUnconditional}

theorem diagonal_coordinates_of_countable_outgoing
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (hout : ∀ α, {β | coordinateEntry T β α ≠ 0}.Countable) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧ ∀ α ∈ Λ, ∀ β ∈ Λ,
      α ≠ β → coordinateEntry T β α = 0 := by
  obtain ⟨Λ, hΛ, hfree⟩ := relation_free_set_of_countable_outgoing
    (fun α β => coordinateEntry T β α ≠ 0) hΓ hout
  exact ⟨Λ, hΛ, fun α hα β hβ hne => not_not.mp (hfree α hα β hβ hne)⟩

theorem diagonal_coordinates_of_countable_incoming
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (hin : ∀ β, {α | coordinateEntry T β α ≠ 0}.Countable) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧ ∀ α ∈ Λ, ∀ β ∈ Λ,
      α ≠ β → coordinateEntry T β α = 0 := by
  obtain ⟨Λ, hΛ, hfree⟩ := relation_free_set_of_countable_incoming
    (fun α β => coordinateEntry T β α ≠ 0) hΓ hin
  exact ⟨Λ, hΛ, fun α hα β hβ hne => not_not.mp (hfree α hα β hβ hne)⟩

/-- The local one-sided alternative in Lemma 4.27. -/
theorem diagonal_coordinates_of_locally_countable_either
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (hlocal : ∀ γ, {η | coordinateEntry T η γ ≠ 0}.Countable ∨
      {η | coordinateEntry T γ η ≠ 0}.Countable) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧ ∀ α ∈ Λ, ∀ β ∈ Λ,
      α ≠ β → coordinateEntry T β α = 0 := by
  obtain ⟨Λ, hΛ, hfree⟩ := relation_free_set_of_locally_countable_either
    (fun α β => coordinateEntry T β α ≠ 0) hΓ hlocal
  exact ⟨Λ, hΛ, fun α hα β hβ hne => not_not.mp (hfree α hα β hβ hne)⟩

/-- Lemma 4.29: apply the actual incoming-support theorem to each target
coordinate, then apply the incoming form of Hajnal's selection. -/
theorem diagonal_coordinates_of_countable_total_dual (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (htotal : HasCountableTotalDual 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧ ∀ α ∈ Λ, ∀ β ∈ Λ,
      α ≠ β → coordinateEntry T β α = 0 :=
  diagonal_coordinates_of_countable_incoming hΓ T
    (countable_incoming_entries hs hnot htotal T)

end UncountableSchauderSum
end ThesisCommon
