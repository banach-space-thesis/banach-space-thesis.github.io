import Posets.OrdinalLiftDerivative

/-! Relative derivative ranks lift through every continuous compact map.
At limit stages, nested compact fibers provide one compatible preimage. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u
namespace Posets
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def ordinalLiftIterate (f : X → Y) (A : Set X) (α : Ordinal.{u}) : Set X :=
  Ordinal.limitRecOn α A (fun _ B => ordinalLiftDerivative f B)
    (fun _ _ g => ⋂ β, ⋂ h, g β h)

@[simp] theorem ordinalLiftIterate_zero (f : X → Y) (A : Set X) :
    ordinalLiftIterate f A (0 : Ordinal.{u}) = A := by simp [ordinalLiftIterate]

@[simp] theorem ordinalLiftIterate_succ (f : X → Y) (A : Set X) (α : Ordinal.{u}) :
    ordinalLiftIterate f A (succ α) = ordinalLiftDerivative f (ordinalLiftIterate f A α) := by
  simp [ordinalLiftIterate]

theorem ordinalLiftIterate_limit (f : X → Y) (A : Set X) {α : Ordinal.{u}}
    (hα : IsSuccLimit α) :
    ordinalLiftIterate f A α = ⋂ β < α, ordinalLiftIterate f A β := by
  unfold ordinalLiftIterate
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]

theorem ordinalLiftIterate_mono (f : X → Y) {A B : Set X} (hAB : A ⊆ B) (α : Ordinal.{u}) :
    ordinalLiftIterate f A α ⊆ ordinalLiftIterate f B α := by
  induction α using Ordinal.limitRecOn with
  | zero => simpa using hAB
  | succ α ih => simpa using ordinalLiftDerivative_mono f ih
  | limit α hα ih =>
    rw [ordinalLiftIterate_limit f A hα, ordinalLiftIterate_limit f B hα]
    exact iInter_mono fun β => iInter_mono fun hβ => ih β hβ

theorem isClosed_ordinalLiftIterate (f : X → Y) {A : Set X} (hA : IsClosed A)
    (α : Ordinal.{u}) : IsClosed (ordinalLiftIterate f A α) := by
  induction α using Ordinal.limitRecOn with
  | zero => simpa using hA
  | succ α ih => simpa using isClosed_ordinalLiftDerivative f ih
  | limit α hα ih =>
    rw [ordinalLiftIterate_limit f A hα]
    exact isClosed_iInter fun β => isClosed_iInter fun hβ => ih β hβ

theorem ordinalLiftIterate_antitone (f : X → Y) (A : Set X) :
    Antitone (ordinalLiftIterate.{u} f A) := by
  intro α β hαβ
  change ordinalLiftIterate f A β ⊆ ordinalLiftIterate f A α
  induction β using Ordinal.limitRecOn generalizing α with
  | zero =>
    have hα : α = 0 := bot_unique hαβ
    subst α
    exact subset_rfl
  | succ β ih =>
    rcases (le_succ_iff_eq_or_le).mp hαβ with h | h
    · subst α; exact subset_rfl
    · rw [ordinalLiftIterate_succ]
      exact (ordinalLiftDerivative_subset f _).trans (ih h)
  | limit β hβ ih =>
    rcases hαβ.eq_or_lt with h | h
    · subst α; exact subset_rfl
    · rw [ordinalLiftIterate_limit f A hβ]
      exact iInter_subset_of_subset α (iInter_subset_of_subset h subset_rfl)

theorem ordinalLiftIterate_subset (f : X → Y) (A : Set X) (α : Ordinal.{u}) :
    ordinalLiftIterate f A α ⊆ A := by
  simpa using ordinalLiftIterate_antitone f A (Ordinal.zero_le α)

theorem isCompact_ordinalLiftIterate [T2Space X] (f : X → Y) {A : Set X}
    (hA : IsCompact A) (α : Ordinal.{u}) : IsCompact (ordinalLiftIterate f A α) :=
  hA.of_isClosed_subset (isClosed_ordinalLiftIterate f hA.isClosed α) (ordinalLiftIterate_subset f A α)

theorem ordinalLiftIterate_image [T2Space X] [T2Space Y]
    (f : X → Y) (hf : Continuous f) {A : Set X} (hA : IsCompact A) (α : Ordinal.{u}) :
    f '' ordinalLiftIterate f A α = ordinalDerived (f '' A) α := by
  induction α using Ordinal.limitRecOn with
  | zero => simp
  | succ α ih =>
    rw [ordinalLiftIterate_succ, ordinalDerived_succ,
      ordinalLiftDerivative_image f hf (isCompact_ordinalLiftIterate f hA α), ih]
  | limit α hα ih =>
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [ordinalDerived_limit _ hα]
      apply mem_iInter₂.mpr
      intro β hβ
      rw [← ih β hβ]
      exact mem_image_of_mem f (ordinalLiftIterate_antitone f A hβ.le hx)
    · intro y hy
      letI : Nonempty (Iio α) := ⟨⟨0, hα.bot_lt⟩⟩
      let S : Iio α → Set X := fun β => ordinalLiftIterate f A β.val ∩ f ⁻¹' {y}
      have hSn (β : Iio α) : (S β).Nonempty := by
        have hyβ := ordinalDerived_antitone (hA.image hf).isClosed β.property.le hy
        rw [← ih β.val β.property] at hyβ
        obtain ⟨x, hx, he⟩ := hyβ
        exact ⟨x, hx, he⟩
      have hSc (β : Iio α) : IsCompact (S β) :=
        (isCompact_ordinalLiftIterate f hA β.val).inter_right (isClosed_singleton.preimage hf)
      have hSd : Directed (· ⊇ ·) S := by
        intro β γ
        refine ⟨max β γ, ?_, ?_⟩
        · exact inter_subset_inter_left _ (ordinalLiftIterate_antitone f A (le_max_left β γ))
        · exact inter_subset_inter_left _ (ordinalLiftIterate_antitone f A (le_max_right β γ))
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        S hSd hSn hSc (fun β => (hSc β).isClosed)
      refine ⟨x, ?_, (mem_iInter.mp hx ⟨0, hα.bot_lt⟩).2⟩
      rw [ordinalLiftIterate_limit f A hα]
      exact mem_iInter₂.mpr fun β hβ => (mem_iInter.mp hx ⟨β, hβ⟩).1

end Posets

