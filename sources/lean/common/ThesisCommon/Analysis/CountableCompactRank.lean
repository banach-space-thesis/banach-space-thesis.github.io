import ThesisCommon.Analysis.OrdinalDerived
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.Family

/-! Cantor--Bendixson termination for countable compact metric spaces.
Perfect nonempty subsets would contain a binary Cantor injection. Removing
an isolated point at every nonempty stage cannot inject all ordinals into
the ambient set. Compactness excludes a first empty limit stage. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon
variable {K : Type u} [MetricSpace K] [CompactSpace K] [Countable K]

private theorem binaryCantor_not_countable : ¬Countable (ℕ → Bool) := by
  intro h
  letI : Countable (ℕ → Bool) := h
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hf (fun m => !(f m m))
  have hdiag := congrFun hn n
  cases hb : f n n <;> simp [hb] at hdiag

theorem countableCompact_perfect_eq_empty {A : Set K} (hA : Perfect A) : A = ∅ := by
  by_contra h
  obtain ⟨f, _, _, hf⟩ := hA.exists_nat_bool_injection (Set.nonempty_iff_ne_empty.mpr h)
  exact binaryCantor_not_countable hf.countable

theorem countableCompact_exists_mem_not_mem_derivedSet {A : Set K}
    (hA : IsCompact A) (hne : A.Nonempty) : ∃ x ∈ A, x ∉ derivedSet A := by
  by_contra! h
  have hp : Perfect A := ⟨hA.isClosed, h⟩
  exact hne.ne_empty (countableCompact_perfect_eq_empty hp)

theorem countableCompact_isCompact_ordinalDerived {A : Set K} (hA : IsCompact A)
    (α : Ordinal.{u}) : IsCompact (ordinalDerived A α) := by
  apply hA.of_isClosed_subset (isClosed_ordinalDerived hA.isClosed α)
  simpa using ordinalDerived_antitone hA.isClosed (show 0 ≤ α from bot_le)

theorem countableCompact_ordinalDerived_eventually_empty {A : Set K} (hA : IsCompact A) :
    ∃ α : Ordinal.{u}, ordinalDerived A α = ∅ := by
  classical
  by_contra! h
  have hn (α : Ordinal.{u}) : (ordinalDerived A α).Nonempty := h α
  have hi (α : Ordinal.{u}) :
      ∃ x ∈ ordinalDerived A α, x ∉ derivedSet (ordinalDerived A α) :=
    countableCompact_exists_mem_not_mem_derivedSet
      (countableCompact_isCompact_ordinalDerived hA α) (hn α)
  let f : Ordinal.{u} → K := fun α => (hi α).choose
  have hne {α β : Ordinal.{u}} (hαβ : α < β) : f α ≠ f β := by
    intro heq
    have hβ : f β ∈ derivedSet (ordinalDerived A α) := by
      have hm := ordinalDerived_antitone hA.isClosed (succ_le_iff.mpr hαβ)
        (hi β).choose_spec.1
      simpa only [ordinalDerived_succ] using hm
    apply (hi α).choose_spec.2
    change f α ∈ derivedSet (ordinalDerived A α)
    rw [heq]
    exact hβ
  apply not_injective_of_ordinal f
  intro α β heq
  rcases lt_trichotomy α β with hlt | he | hgt
  · exact (hne hlt heq).elim
  · exact he
  · exact (hne hgt heq.symm).elim

theorem countableCompact_ordinalDerived_nonempty_limit {A : Set K} (hA : IsCompact A)
    {α : Ordinal.{u}} (hα : IsSuccLimit α)
    (hne : ∀ β < α, (ordinalDerived A β).Nonempty) :
    (ordinalDerived A α).Nonempty := by
  letI : Nonempty (Iio α) := ⟨⟨0, hα.bot_lt⟩⟩
  have hd : Directed (· ⊇ ·) (fun β : Iio α => ordinalDerived A β.val) := by
    intro β γ
    refine ⟨⟨max β.val γ.val, show max β.val γ.val < α from
      max_lt β.property γ.property⟩, ?_, ?_⟩
    · exact ordinalDerived_antitone hA.isClosed (le_max_left _ _)
    · exact ordinalDerived_antitone hA.isClosed (le_max_right _ _)
  have hi := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun β : Iio α => ordinalDerived A β.val) hd
    (fun β => hne β.val β.property)
    (fun β => countableCompact_isCompact_ordinalDerived hA β.val)
    (fun β => isClosed_ordinalDerived hA.isClosed β.val)
  rw [ordinalDerived_limit A hα]
  simpa only [iInter_subtype] using hi

theorem countableCompact_ordinalDerived_finite_of_succ_empty {A : Set K}
    (hA : IsCompact A) {α : Ordinal.{u}} (h : ordinalDerived A (succ α) = ∅) :
    (ordinalDerived A α).Finite := by
  by_contra! hinf
  have hinf' : (ordinalDerived A α).Infinite := hinf
  obtain ⟨a, _, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact
    (countableCompact_isCompact_ordinalDerived hA α) subset_rfl
  have : a ∈ ordinalDerived A (succ α) := by
    rw [ordinalDerived_succ]
    exact hacc
  simpa [h] using this

/-- Every nonempty countable compact metric set has a finite nonempty
terminal Cantor--Bendixson derivative. -/
theorem countableCompact_exists_finite_nonempty_derivative {A : Set K}
    (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ α : Ordinal.{u}, (ordinalDerived A α).Finite ∧ (ordinalDerived A α).Nonempty ∧
      ordinalDerived A (succ α) = ∅ := by
  let E : Set Ordinal.{u} := {α | ordinalDerived A α = ∅}
  have hE : E.Nonempty := countableCompact_ordinalDerived_eventually_empty hA
  let δ := sInf E
  have hδ : ordinalDerived A δ = ∅ := csInf_mem hE
  have hbefore {β : Ordinal.{u}} (hβ : β < δ) : (ordinalDerived A β).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    exact hβ.not_ge (csInf_le' (show β ∈ E from he))
  rcases Ordinal.zero_or_succ_or_isSuccLimit δ with hzero | ⟨α, hsucc⟩ | hlimit
  · have he : A = ∅ := by simpa [hzero] using hδ
    exact (hne.ne_empty he).elim
  · refine ⟨α, ?_, ?_, ?_⟩
    · exact countableCompact_ordinalDerived_finite_of_succ_empty hA (hsucc ▸ hδ)
    · exact hbefore (hsucc ▸ lt_succ α)
    · exact hsucc ▸ hδ
  · exact ((countableCompact_ordinalDerived_nonempty_limit hA hlimit
      (fun β hβ => hbefore hβ)).ne_empty hδ).elim

end ThesisCommon
