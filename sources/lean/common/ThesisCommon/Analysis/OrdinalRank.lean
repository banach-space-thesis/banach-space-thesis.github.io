import ThesisCommon.Analysis.OrdinalScattered

/-! Existence of a finite nonempty last derivative of a nonempty compact
ordinal set. Termination follows from the impossibility of injecting all
ordinals into a bounded ordinal set; compactness excludes a first empty
derivative at a limit ordinal. -/
noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

theorem ordinalDerived_eventually_empty {A : Set Ordinal.{u}} (hA : IsCompact A) :
    ∃ α : Ordinal.{u}, ordinalDerived A α = ∅ := by
  classical
  by_contra! h
  have hn (α : Ordinal.{u}) : (ordinalDerived A α).Nonempty := h α
  letI : Small.{u} A := Ordinal.bddAbove_iff_small.mp hA.bddAbove
  let f : Ordinal.{u} → A := fun α => ⟨sInf (ordinalDerived A α), by
    have hsub : ordinalDerived A α ⊆ A := by
      simpa using ordinalDerived_antitone hA.isClosed (show 0 ≤ α from bot_le)
    exact hsub (csInf_mem (hn α))⟩
  have hne {α β : Ordinal.{u}} (hαβ : α < β) : f α ≠ f β := by
    intro heq
    have hβ : sInf (ordinalDerived A β) ∈ derivedSet (ordinalDerived A α) := by
      have hm := ordinalDerived_antitone hA.isClosed (succ_le_iff.mpr hαβ)
        (csInf_mem (hn β))
      simpa using hm
    have heq' : sInf (ordinalDerived A α) = sInf (ordinalDerived A β) :=
      congrArg Subtype.val heq
    exact ordinal_sInf_not_mem_derivedSet (hn α) (heq' ▸ hβ)
  apply not_injective_of_ordinal f
  intro α β heq
  rcases lt_trichotomy α β with hlt | he | hgt
  · exact (hne hlt heq).elim
  · exact he
  · exact (hne hgt heq.symm).elim

theorem ordinalDerived_nonempty_limit {A : Set Ordinal.{u}} (hA : IsCompact A)
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
    (fun β => isCompact_ordinalDerived hA β.val)
    (fun β => isClosed_ordinalDerived hA.isClosed β.val)
  rw [ordinalDerived_limit A hα]
  simpa only [iInter_subtype] using hi

/-- Every nonempty compact ordinal set has a characteristic rank, expressed
without a convention about the endpoint of its finite ordinal model. -/
theorem ordinal_exists_finite_nonempty_derivative {A : Set Ordinal.{u}}
    (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ α : Ordinal.{u}, (ordinalDerived A α).Finite ∧ (ordinalDerived A α).Nonempty ∧
      ordinalDerived A (succ α) = ∅ := by
  let E : Set Ordinal.{u} := {α | ordinalDerived A α = ∅}
  have hE : E.Nonempty := ordinalDerived_eventually_empty hA
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
    · exact ordinalDerived_finite_of_succ_empty hA (hsucc ▸ hδ)
    · exact hbefore (hsucc ▸ lt_succ α)
    · exact hsucc ▸ hδ
  · exact ((ordinalDerived_nonempty_limit hA hlimit (fun β hβ => hbefore hβ)).ne_empty hδ).elim

end ThesisCommon
