import ThesisCommon.Analysis.JamesTreeSegments
import Mathlib.Order.OrderIsoNat
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! A genuine breadth-first enumeration of the full binary tree. Within
each level we order by a binary code; every finite initial set is closed
under taking prefixes. -/
noncomputable section
namespace ThesisCommon

def dyadicTreeCode : DyadicTreeNode → ℕ
  | [] => 1
  | false :: t => 2 * dyadicTreeCode t
  | true :: t => 2 * dyadicTreeCode t + 1

theorem dyadicTreeCode_pos (t : DyadicTreeNode) : 0 < dyadicTreeCode t := by
  induction t with
  | nil => simp [dyadicTreeCode]
  | cons b t ih => cases b <;> simp only [dyadicTreeCode] <;> omega

theorem dyadicTreeCode_injective : Function.Injective dyadicTreeCode := by
  intro s
  induction s with
  | nil =>
      intro t h
      cases t with
      | nil => rfl
      | cons b t =>
          have ht := dyadicTreeCode_pos t
          cases b <;> simp only [dyadicTreeCode] at h <;> omega
  | cons b s ih =>
      intro t h
      cases t with
      | nil =>
          have hs := dyadicTreeCode_pos s
          cases b <;> simp only [dyadicTreeCode] at h <;> omega
      | cons c t =>
          cases b <;> cases c <;> simp only [dyadicTreeCode] at h
          · exact congrArg (List.cons false) (ih (by omega))
          · omega
          · omega
          · exact congrArg (List.cons true) (ih (by omega))

theorem dyadicTreeCode_append_le (s t : DyadicTreeNode) :
    dyadicTreeCode s ≤ dyadicTreeCode (s ++ t) := by
  induction s with
  | nil => simpa [dyadicTreeCode] using dyadicTreeCode_pos t
  | cons b s ih => cases b <;> simp only [List.cons_append, dyadicTreeCode] <;> omega

theorem dyadicTreeCode_le_of_prefix {s t : DyadicTreeNode} (h : s.IsPrefix t) :
    dyadicTreeCode s ≤ dyadicTreeCode t := by
  obtain ⟨u, rfl⟩ := h
  exact dyadicTreeCode_append_le s u

theorem dyadicTreeCode_bounds (t : DyadicTreeNode) :
    2 ^ t.length ≤ dyadicTreeCode t ∧ dyadicTreeCode t < 2 ^ (t.length + 1) := by
  induction t with
  | nil => norm_num [dyadicTreeCode]
  | cons b t ih =>
      cases b <;> simp only [List.length_cons, dyadicTreeCode, pow_succ] at * <;> omega

private instance dyadicTreeCode_range_infinite : Infinite (Set.range dyadicTreeCode) :=
  Set.infinite_coe_iff.mpr (Set.infinite_range_of_injective dyadicTreeCode_injective)

def dyadicTreeEnumeration : ℕ ≃ DyadicTreeNode :=
  (Nat.Subtype.orderIsoOfNat (Set.range dyadicTreeCode)).toEquiv.trans
    (Equiv.ofInjective dyadicTreeCode dyadicTreeCode_injective).symm

theorem dyadicTreeEnumeration_code (n : ℕ) :
    dyadicTreeCode (dyadicTreeEnumeration n) =
      (Nat.Subtype.orderIsoOfNat (Set.range dyadicTreeCode) n).val := by
  exact congrArg Subtype.val
    ((Equiv.ofInjective dyadicTreeCode dyadicTreeCode_injective).apply_symm_apply _)

theorem dyadicTreeEnumeration_code_strictMono :
    StrictMono (fun n => dyadicTreeCode (dyadicTreeEnumeration n)) := by
  intro m n h
  simp only [dyadicTreeEnumeration_code]
  exact (Nat.Subtype.orderIsoOfNat (Set.range dyadicTreeCode)).strictMono h

theorem dyadicTreeEnumeration_prefix_index {s t : DyadicTreeNode} (h : s.IsPrefix t) :
    dyadicTreeEnumeration.symm s ≤ dyadicTreeEnumeration.symm t := by
  apply dyadicTreeEnumeration_code_strictMono.le_iff_le.mp
  simpa only [Equiv.apply_symm_apply] using dyadicTreeCode_le_of_prefix h

theorem dyadicTreeEnumeration_length_mono :
    Monotone (fun n => (dyadicTreeEnumeration n).length) := by
  intro m n hmn
  have hc := dyadicTreeEnumeration_code_strictMono.monotone hmn
  have hm := (dyadicTreeCode_bounds (dyadicTreeEnumeration m)).1
  have hn := (dyadicTreeCode_bounds (dyadicTreeEnumeration n)).2
  change (dyadicTreeEnumeration m).length ≤ (dyadicTreeEnumeration n).length
  by_contra h
  have hl : (dyadicTreeEnumeration n).length + 1 ≤ (dyadicTreeEnumeration m).length :=
    by omega
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hl
  omega

def dyadicEnumerationInitial (N : ℕ) : Finset DyadicTreeNode :=
  (Finset.range N).map dyadicTreeEnumeration.toEmbedding

@[simp] theorem mem_dyadicEnumerationInitial (t : DyadicTreeNode) (N : ℕ) :
    t ∈ dyadicEnumerationInitial N ↔ dyadicTreeEnumeration.symm t < N := by
  simp [dyadicEnumerationInitial]

theorem dyadicEnumerationInitial_prefix_closed {N : ℕ} {s t : DyadicTreeNode}
    (ht : t ∈ dyadicEnumerationInitial N) (hst : s.IsPrefix t) :
    s ∈ dyadicEnumerationInitial N := by
  rw [mem_dyadicEnumerationInitial] at ht ⊢
  exact (dyadicTreeEnumeration_prefix_index hst).trans_lt ht

end ThesisCommon
