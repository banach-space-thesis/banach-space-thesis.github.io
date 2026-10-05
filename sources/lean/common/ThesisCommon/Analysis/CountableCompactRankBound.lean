import ThesisCommon.Analysis.CountableCompactRank
import ThesisCommon.Analysis.OrdinalBakerLocality

/-! Countability of Cantor--Bendixson ranks and strict rank reduction on
compact pieces disjoint from a prescribed derivative. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon
variable {K : Type u} [MetricSpace K] [CompactSpace K] [Countable K]

theorem countableCompact_rank_card_le_aleph0 {A : Set K} (hA : IsCompact A)
    {α : Ordinal.{u}} (hne : (ordinalDerived A α).Nonempty) :
    α.card ≤ Cardinal.aleph0 := by
  classical
  have hn (β : Iio α) : (ordinalDerived A β.val).Nonempty :=
    hne.mono (ordinalDerived_antitone hA.isClosed β.property.le)
  have hi (β : Iio α) :
      ∃ x ∈ ordinalDerived A β.val, x ∉ derivedSet (ordinalDerived A β.val) :=
    countableCompact_exists_mem_not_mem_derivedSet
      (countableCompact_isCompact_ordinalDerived hA β.val) (hn β)
  let f : Iio α → K := fun β => (hi β).choose
  have hne' {β γ : Iio α} (hβγ : β.val < γ.val) : f β ≠ f γ := by
    intro heq
    have hγ : f γ ∈ derivedSet (ordinalDerived A β.val) := by
      have hm := ordinalDerived_antitone hA.isClosed (succ_le_iff.mpr hβγ)
        (hi γ).choose_spec.1
      simpa only [ordinalDerived_succ] using hm
    apply (hi β).choose_spec.2
    change f β ∈ derivedSet (ordinalDerived A β.val)
    rw [heq]
    exact hγ
  have hf : Function.Injective f := by
    intro β γ heq
    rcases lt_trichotomy β.val γ.val with hlt | he | hgt
    · exact (hne' hlt heq).elim
    · exact Subtype.ext he
    · exact (hne' hgt heq.symm).elim
  haveI : Countable (Iio α) := hf.countable
  have hc : Cardinal.mk (Iio α) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  rw [Ordinal.mk_Iio_ordinal] at hc
  exact Cardinal.lift_le_aleph0.mp hc

theorem countableCompact_exists_countable_finite_nonempty_derivative {A : Set K}
    (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ α : Ordinal.{u}, α.card ≤ Cardinal.aleph0 ∧
      (ordinalDerived A α).Finite ∧ (ordinalDerived A α).Nonempty ∧
      ordinalDerived A (succ α) = ∅ := by
  obtain ⟨α, hfin, hn, hempty⟩ := countableCompact_exists_finite_nonempty_derivative hA hne
  exact ⟨α, countableCompact_rank_card_le_aleph0 hA hn, hfin, hn, hempty⟩

theorem countableCompact_exists_terminal_rank_lt {A : Set K} (hA : IsCompact A)
    (hne : A.Nonempty) {α : Ordinal.{u}} (hempty : ordinalDerived A α = ∅) :
    ∃ β < α, (ordinalDerived A β).Finite ∧ (ordinalDerived A β).Nonempty ∧
      ordinalDerived A (succ β) = ∅ := by
  obtain ⟨β, hfin, hn, hb⟩ := countableCompact_exists_finite_nonempty_derivative hA hne
  refine ⟨β, ?_, hfin, hn, hb⟩
  by_contra h
  have hs := ordinalDerived_antitone hA.isClosed (le_of_not_gt h)
  have he := hn.mono hs
  simpa [hempty] using he

/-- Every nonempty compact piece disjoint from the α-th derivative has
terminal rank strictly below α. This is the induction decrease needed in
the countable compact-space classification. -/
theorem countableCompact_piece_rank_lt {A B : Set K} (hA : IsCompact A)
    (hB : IsCompact B) (hBA : B ⊆ A) (hne : B.Nonempty) {α : Ordinal.{u}}
    (hdisj : Disjoint B (ordinalDerived A α)) :
    ∃ β < α, (ordinalDerived B β).Finite ∧ (ordinalDerived B β).Nonempty ∧
      ordinalDerived B (succ β) = ∅ := by
  apply countableCompact_exists_terminal_rank_lt hB hne
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxB : x ∈ B := by
    have hsub := ordinalDerived_antitone hB.isClosed (show 0 ≤ α from bot_le)
    simpa using hsub hx
  exact Set.disjoint_left.mp hdisj hxB (ordinalDerived_mono hBA α hx)

theorem countableCompact_clopen_piece_rank_lt {A U : Set K} (hA : IsCompact A)
    (hU : IsClopen U) (hne : (A ∩ U).Nonempty) {α : Ordinal.{u}}
    (hdisj : Disjoint U (ordinalDerived A α)) :
    ∃ β < α, (ordinalDerived (A ∩ U) β).Finite ∧
      (ordinalDerived (A ∩ U) β).Nonempty ∧ ordinalDerived (A ∩ U) (succ β) = ∅ :=
  countableCompact_piece_rank_lt hA (hA.inter_right hU.isClosed) inter_subset_left hne
    (hdisj.mono_left inter_subset_right)

end ThesisCommon
