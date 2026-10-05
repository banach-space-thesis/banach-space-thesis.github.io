import ThesisCommon.Analysis.UncountableSchauderIncomingSupport
import ThesisCommon.Analysis.UncountableSchauderCountableSupport
import ThesisCommon.Analysis.SeparableTotalDual
import ThesisCommon.Analysis.TwoSidedFreeSet

/-! Two-sided countable coordinate entries give a full-cardinality diagonal
coordinate set. For separable coefficients, both support conditions are
proved on the genuine norm-series space. This is the source's two-sided
free-set argument; it imposes the section's uncountability explicitly. -/
noncomputable section
open TopologicalSpace
open scoped Cardinal
namespace ThesisCommon
namespace UncountableSchauderSum
variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {b : NormalizedSchauderFamily 𝕜 Γ E} {hb : b.IsOneUnconditional}

/-- The actual matrix entry as an operator on the whole coordinate sum. -/
def coordinateEntry
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (β α : Γ) : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X :=
  ((coordinateProjection {β}).comp T).comp (coordinateProjection {α})

theorem coordinateEntry_apply
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (β α : Γ) (x : UncountableSchauderSum b hb X) :
    coordinateEntry T β α x = single β ((T (single α (x α))) β) := by
  simp only [coordinateEntry, ContinuousLinearMap.comp_apply, coordinateProjection_singleton]

theorem countable_outgoing_entries_of_separable [SeparableSpace X]
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X) (α : Γ) :
    {β | coordinateEntry T β α ≠ 0}.Countable := by
  let S := T.comp (singleL (b := b) (hb := hb) (Y := X) α)
  obtain ⟨Λ, hΛ, hS⟩ := separable_countable_support (isSeparable_range S.continuous)
  apply hΛ.mono
  intro β hβ
  by_contra hβΛ
  apply hβ
  apply ContinuousLinearMap.ext
  intro x
  have hz := hS (Set.mem_range_self (x α)) β hβΛ
  change T (single α (x α)) β = 0 at hz
  rw [coordinateEntry_apply, hz]
  change singleL (b := b) (hb := hb) (Y := X) β 0 = 0
  exact map_zero _

theorem countable_incoming_entries (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (htotal : HasCountableTotalDual 𝕜 X)
    (T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X) (β : Γ) :
    {α | coordinateEntry T β α ≠ 0}.Countable := by
  obtain ⟨Δ, hΔ, hz⟩ := operator_countable_incoming_support hs hnot htotal
    ((coordinate β).comp T)
  apply hΔ.mono
  intro α hα
  by_contra hαΔ
  apply hα
  apply ContinuousLinearMap.ext
  intro x
  have hzero := DFunLike.congr_fun (hz α hαΔ) x
  change (T (coordinateProjection (b := b) (hb := hs.1) (Y := X) {α} x)) β = 0 at hzero
  rw [coordinateProjection_singleton] at hzero
  rw [coordinateEntry_apply, hzero]
  change singleL (b := b) (hb := hs.1) (Y := X) β 0 = 0
  exact map_zero _

/-- The two-sided alternative in 4.27, with the required uncountable regime. -/
theorem diagonal_coordinates_of_two_sided_countable
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (hout : ∀ α, {β | coordinateEntry T β α ≠ 0}.Countable)
    (hin : ∀ β, {α | coordinateEntry T β α ≠ 0}.Countable) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧ ∀ α ∈ Λ, ∀ β ∈ Λ,
      α ≠ β → coordinateEntry T β α = 0 := by
  obtain ⟨Λ, hΛ, hfree⟩ := twoSided_countable_free_set
    (fun α => {β | coordinateEntry T β α ≠ 0}) ⟨hout, hin⟩ hΓ
  refine ⟨Λ, hΛ, ?_⟩
  intro α hα β hβ hne
  exact not_not.mp (hfree α hα β hβ hne).2

/-- The full coordinate selection of 4.30 in the section's uncountable
regime; no regularity or cofinality premise is added. -/
theorem diagonal_coordinates_of_separable (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) [SeparableSpace X]
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧ ∀ α ∈ Λ, ∀ β ∈ Λ,
      α ≠ β → coordinateEntry T β α = 0 :=
  diagonal_coordinates_of_two_sided_countable hΓ T
    (countable_outgoing_entries_of_separable T)
    (countable_incoming_entries hs hnot (hasCountableTotalDual_of_separable 𝕜 X) T)

end UncountableSchauderSum
end ThesisCommon
