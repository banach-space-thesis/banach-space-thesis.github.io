import ThesisCommon.Analysis.OrdinalDerived
import Mathlib.Topology.Order.Compact

/-! The least point of a nonempty ordinal set is never an accumulation
point. Consequently the transfinite derivatives strictly decrease while
nonempty, and a compact last nonempty derivative is finite. -/
noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

theorem ordinal_sInf_not_mem_derivedSet {A : Set Ordinal.{u}} (_hne : A.Nonempty) :
    sInf A ∉ derivedSet A := by
  intro h
  have ha : Ordinal.IsAcc (sInf A) A := h
  obtain ⟨b, hbA, hb0, hba⟩ := ha.forall_lt 0 ha.pos
  exact hba.not_ge (csInf_le' hbA)

theorem ordinal_exists_mem_not_mem_derivedSet {A : Set Ordinal.{u}} (hne : A.Nonempty) :
    ∃ a ∈ A, a ∉ derivedSet A :=
  ⟨sInf A, csInf_mem hne, ordinal_sInf_not_mem_derivedSet hne⟩

theorem ordinal_derivedSet_ne_self {A : Set Ordinal.{u}} (hne : A.Nonempty) :
    derivedSet A ≠ A := by
  intro h
  apply ordinal_sInf_not_mem_derivedSet hne
  rw [h]
  exact csInf_mem hne

theorem ordinal_perfect_eq_empty {A : Set Ordinal.{u}} (hA : Perfect A) : A = ∅ := by
  by_contra h
  exact ordinal_derivedSet_ne_self (nonempty_iff_ne_empty.mpr h)
    ((perfect_iff_eq_derivedSet.mp hA).symm)

theorem ordinalDerived_succ_ssubset {A : Set Ordinal.{u}} (hA : IsClosed A)
    {α : Ordinal.{u}} (hne : (ordinalDerived A α).Nonempty) :
    ordinalDerived A (succ α) ⊂ ordinalDerived A α := by
  rw [ordinalDerived_succ]
  exact (ssubset_iff_subset_ne).mpr
    ⟨(isClosed_iff_derivedSet_subset _).mp (isClosed_ordinalDerived hA α),
      ordinal_derivedSet_ne_self hne⟩

theorem isCompact_ordinalDerived {A : Set Ordinal.{u}} (hA : IsCompact A)
    (α : Ordinal.{u}) : IsCompact (ordinalDerived A α) := by
  apply hA.of_isClosed_subset (isClosed_ordinalDerived hA.isClosed α)
  simpa using ordinalDerived_antitone hA.isClosed (show 0 ≤ α from bot_le)

theorem ordinalDerived_finite_of_succ_empty {A : Set Ordinal.{u}} (hA : IsCompact A)
    {α : Ordinal.{u}} (h : ordinalDerived A (succ α) = ∅) :
    (ordinalDerived A α).Finite := by
  by_contra! hinf
  have hinf' : (ordinalDerived A α).Infinite := hinf
  obtain ⟨a, ha, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact
    (isCompact_ordinalDerived hA α) subset_rfl
  have : a ∈ ordinalDerived A (succ α) := by
    rw [ordinalDerived_succ]
    exact hacc
  simpa [h] using this

end ThesisCommon
