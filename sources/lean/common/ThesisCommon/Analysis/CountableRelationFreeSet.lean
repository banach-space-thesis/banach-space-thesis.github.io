import ThesisCommon.Analysis.HajnalFreeSet
import ThesisCommon.Analysis.FilterCoordinateCopy

/-! One-sided countable relations have full-sized free subsets above ℵ₁.
The local either-or version first chooses a full-sized set with one common
orientation. This preserves every cross-coordinate interaction. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ : Type u}

theorem relation_free_set_of_countable_outgoing (r : Γ → Γ → Prop)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hr : ∀ α, {β | r α β}.Countable) :
    ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧
      ∀ α ∈ H, ∀ β ∈ H, α ≠ β → ¬ r α β := by
  let F (α : Γ) : Set Γ := {β | β ≠ α ∧ r α β}
  have hF (α : Γ) : Cardinal.mk (F α) < Cardinal.aleph 1 :=
    (Cardinal.countable_iff_lt_aleph_one _).mp ((hr α).mono (fun _ h => h.2))
  obtain ⟨H, hcard, hfree⟩ := hajnal_free_set F (Cardinal.aleph 1)
    (Cardinal.aleph0_lt_aleph_one.trans hΓ).le hΓ hF
  refine ⟨H, hcard, ?_⟩
  intro α hα β hβ hne hrαβ
  exact (hfree α hα β hβ hne).2 ⟨hne.symm, hrαβ⟩

theorem relation_free_set_of_countable_incoming (r : Γ → Γ → Prop)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hr : ∀ β, {α | r α β}.Countable) :
    ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧
      ∀ α ∈ H, ∀ β ∈ H, α ≠ β → ¬ r α β := by
  obtain ⟨H, hcard, hfree⟩ := relation_free_set_of_countable_outgoing
    (fun α β => r β α) hΓ hr
  exact ⟨H, hcard, fun α hα β hβ hne => hfree β hβ α hα hne.symm⟩

/-- Restrict the relation to S, apply Hajnal there, and map the free subset
back through the actual subtype inclusion. -/
theorem relation_free_set_on_of_countable_outgoing (r : Γ → Γ → Prop)
    (S : Set Γ) (hS : Cardinal.aleph 1 < Cardinal.mk S)
    (hr : ∀ α ∈ S, {β | r α β}.Countable) :
    ∃ H : Set Γ, H ⊆ S ∧ Cardinal.mk H = Cardinal.mk S ∧
      ∀ α ∈ H, ∀ β ∈ H, α ≠ β → ¬ r α β := by
  classical
  obtain ⟨A, hAcard, hAfree⟩ := relation_free_set_of_countable_outgoing
    (fun α β : S => r α.val β.val) hS
    (fun α => (hr α.val α.property).preimage Subtype.val_injective)
  let f : A → Γ := fun α => α.val.val
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  refine ⟨Set.range f, ?_, (Cardinal.mk_range_eq f hf).trans hAcard, ?_⟩
  · rintro _ ⟨α, rfl⟩
    exact α.val.property
  · rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩ hne
    exact hAfree α.val α.property β.val β.property
      (fun h => hne (congrArg Subtype.val h))

/-- The one-sided choice may depend on the point. Select a full-sized
monochromatic subset before fixing an orientation and applying Hajnal. -/
theorem relation_free_set_of_locally_countable_either (r : Γ → Γ → Prop)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hr : ∀ α, {β | r α β}.Countable ∨ {β | r β α}.Countable) :
    ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧
      ∀ α ∈ H, ∀ β ∈ H, α ≠ β → ¬ r α β := by
  classical
  haveI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp
    (Cardinal.aleph0_lt_aleph_one.trans hΓ).le
  let S : Set Γ := {α | {β | r α β}.Countable}
  rcases cardinal_eq_of_set_or_compl S with hS | hS
  · obtain ⟨H, _hHS, hcard, hfree⟩ := relation_free_set_on_of_countable_outgoing r S
      (by simpa only [hS] using hΓ) (fun _ h => h)
    exact ⟨H, hcard.trans hS, hfree⟩
  · obtain ⟨H, _hHS, hcard, hfree⟩ := relation_free_set_on_of_countable_outgoing
      (fun α β => r β α) Sᶜ (by simpa only [hS] using hΓ)
      (fun α hα => (hr α).resolve_left hα)
    exact ⟨H, hcard.trans hS, fun α hα β hβ hne => hfree β hβ α hα hne.symm⟩

end ThesisCommon
