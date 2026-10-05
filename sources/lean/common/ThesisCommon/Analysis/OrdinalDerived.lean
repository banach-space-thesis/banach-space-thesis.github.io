import Mathlib.Topology.DerivedSet
import Mathlib.SetTheory.Ordinal.Topology

/-! Transfinite derived sets with the manuscript's successor and limit
conventions. The finite-union calculation is proved before any classification
of compact ordinal spaces is invoked. -/
noncomputable section
open Set Order
universe u v
namespace ThesisCommon
variable {K : Type v} [TopologicalSpace K]

def ordinalDerived (A : Set K) (α : Ordinal.{u}) : Set K :=
  Ordinal.limitRecOn α A (fun _ B => derivedSet B)
    (fun _ _ f => ⋂ β, ⋂ h, f β h)

@[simp] theorem ordinalDerived_zero (A : Set K) : ordinalDerived A (0 : Ordinal.{u}) = A := by
  simp [ordinalDerived]

@[simp] theorem ordinalDerived_succ (A : Set K) (α : Ordinal.{u}) :
    ordinalDerived A (succ α) = derivedSet (ordinalDerived A α) := by
  simp [ordinalDerived]

theorem ordinalDerived_limit (A : Set K) {α : Ordinal.{u}} (hα : IsSuccLimit α) :
    ordinalDerived A α = ⋂ β < α, ordinalDerived A β := by
  unfold ordinalDerived
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]

theorem ordinalDerived_mono {A B : Set K} (hAB : A ⊆ B) (α : Ordinal.{u}) :
    ordinalDerived A α ⊆ ordinalDerived B α := by
  induction α using Ordinal.limitRecOn with
  | zero => simpa using hAB
  | succ α ih => simpa using derivedSet_mono _ _ ih
  | limit α hα ih =>
      rw [ordinalDerived_limit A hα, ordinalDerived_limit B hα]
      exact iInter_mono fun β => iInter_mono fun hβ => ih β hβ

theorem isClosed_ordinalDerived [T1Space K] {A : Set K} (hA : IsClosed A)
    (α : Ordinal.{u}) : IsClosed (ordinalDerived A α) := by
  induction α using Ordinal.limitRecOn with
  | zero => simpa using hA
  | succ α _ => simp
  | limit α hα ih =>
      rw [ordinalDerived_limit A hα]
      exact isClosed_iInter fun β => isClosed_iInter fun hβ => ih β hβ

theorem ordinalDerived_antitone [T1Space K] {A : Set K} (hA : IsClosed A) :
    Antitone (ordinalDerived.{u, v} A) := by
  intro α β hαβ
  change ordinalDerived A β ⊆ ordinalDerived A α
  induction β using Ordinal.limitRecOn generalizing α with
  | zero =>
      have hα : α = 0 := bot_unique hαβ
      subst α
      exact subset_rfl
  | succ β ih =>
      rcases (le_succ_iff_eq_or_le).mp hαβ with h | h
      · subst α; exact subset_rfl
      · simpa only [ordinalDerived_succ] using ((isClosed_iff_derivedSet_subset _).mp
          (isClosed_ordinalDerived hA β)).trans (ih h)
  | limit β hβ ih =>
      rcases hαβ.eq_or_lt with h | h
      · subst α; exact subset_rfl
      · rw [ordinalDerived_limit A hβ]
        exact iInter_subset_of_subset α (iInter_subset_of_subset h subset_rfl)

theorem ordinalDerived_union [T1Space K] {A B : Set K}
    (hA : IsClosed A) (hB : IsClosed B) (α : Ordinal.{u}) :
    ordinalDerived (A ∪ B) α = ordinalDerived A α ∪ ordinalDerived B α := by
  induction α using Ordinal.limitRecOn with
  | zero => simp
  | succ α ih => rw [ordinalDerived_succ, ih, derivedSet_union,
      ← ordinalDerived_succ, ← ordinalDerived_succ]
  | limit α hα ih =>
      apply Subset.antisymm
      · intro x hx
        by_contra! h
        have hxA : x ∉ ⋂ β < α, ordinalDerived A β := by
          rw [← ordinalDerived_limit A hα]; exact fun hx => h (Or.inl hx)
        have hxB : x ∉ ⋂ β < α, ordinalDerived B β := by
          rw [← ordinalDerived_limit B hα]; exact fun hx => h (Or.inr hx)
        simp only [mem_iInter, not_forall] at hxA hxB
        obtain ⟨β, hβ, hxβ⟩ := hxA
        obtain ⟨γ, hγ, hxγ⟩ := hxB
        have hm : max β γ < α := max_lt hβ hγ
        have hxM : x ∈ ordinalDerived (A ∪ B) (max β γ) := by
          rw [ordinalDerived_limit (A ∪ B) hα] at hx
          exact mem_iInter₂.mp hx (max β γ) hm
        rw [ih (max β γ) hm] at hxM
        rcases hxM with hxM | hxM
        · exact hxβ (ordinalDerived_antitone hA (le_max_left _ _) hxM)
        · exact hxγ (ordinalDerived_antitone hB (le_max_right _ _) hxM)
      · exact union_subset (ordinalDerived_mono subset_union_left α)
          (ordinalDerived_mono subset_union_right α)

end ThesisCommon
