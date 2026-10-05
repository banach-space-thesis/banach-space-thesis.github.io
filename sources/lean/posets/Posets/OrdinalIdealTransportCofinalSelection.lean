import JLMS.OrdinalClosedIntersections
import Mathlib.SetTheory.Cardinal.Regular

/-! A cofinal color below a regular initial ordinal contains a full increasing
copy of that ordinal. This is the selection used for the diagonal branch. -/
noncomputable section
namespace Posets

theorem exists_regularOrdinal_cofinal_selection {c : Cardinal.{0}}
    (hc : c.IsRegular) (p : Set.Iio c.ord → Prop)
    (hp : ∀ i : Set.Iio c.ord, ∃ j : Set.Iio c.ord, i < j ∧ p j) :
    ∃ e : Set.Iio c.ord → Set.Iio c.ord, StrictMono e ∧
      (∀ i, i ≤ e i) ∧ ∀ i, p (e i) := by
  classical
  let s : Set Ordinal.{0} := {ξ | ∀ hξ : ξ < c.ord, p ⟨ξ, hξ⟩}
  have hs : ¬ BddAbove s := by
    rintro ⟨β, hβ⟩
    have hm : Order.succ (max β c.ord) ∈ s := by
      intro h
      exact (not_lt_of_ge ((le_max_right β c.ord).trans (Order.le_succ _)) h).elim
    exact (Order.lt_succ (max β c.ord)).not_ge ((hβ hm).trans (le_max_left _ _))
  have hcofinal : ∀ β < c.ord, ∃ δ < c.ord, β < δ ∧ δ ∈ s := by
    intro β hβ
    obtain ⟨j, hj, hpj⟩ := hp ⟨β, hβ⟩
    exact ⟨j.val, j.property, hj, fun _ => hpj⟩
  have hbound (i : Set.Iio c.ord) : Ordinal.enumOrd s i.val < c.ord :=
    JLMS.enumOrd_lt_of_cofinal_below
      (fun ξ hξ => by simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hξ)
      hcofinal i.val i.property
  let e (i : Set.Iio c.ord) : Set.Iio c.ord := ⟨Ordinal.enumOrd s i.val, hbound i⟩
  exact ⟨e, fun _ _ hij => Ordinal.enumOrd_strictMono hs hij,
    fun i => Ordinal.le_enumOrd_self hs, fun i => Ordinal.enumOrd_mem hs i.val (hbound i)⟩

theorem exists_regularOrdinal_twoColor_selection {c : Cardinal.{0}}
    (hc : c.IsRegular) (p q : Set.Iio c.ord → Prop) (hpq : ∀ i, p i ∨ q i) :
    (∃ e : Set.Iio c.ord → Set.Iio c.ord, StrictMono e ∧
      (∀ i, i ≤ e i) ∧ ∀ i, p (e i)) ∨
    (∃ e : Set.Iio c.ord → Set.Iio c.ord, StrictMono e ∧
      (∀ i, i ≤ e i) ∧ ∀ i, q (e i)) := by
  classical
  by_cases hp : ∀ i : Set.Iio c.ord, ∃ j : Set.Iio c.ord, i < j ∧ p j
  · exact Or.inl (exists_regularOrdinal_cofinal_selection hc p hp)
  · push_neg at hp
    obtain ⟨i, hi⟩ := hp
    right
    apply exists_regularOrdinal_cofinal_selection hc q
    intro j
    let k : Set.Iio c.ord := ⟨Order.succ (max i.val j.val),
      (Cardinal.isSuccLimit_ord hc.aleph0_le).succ_lt (max_lt i.property j.property)⟩
    have hik : i < k := (le_max_left i.val j.val).trans_lt (Order.lt_succ _)
    have hjk : j < k := (le_max_right i.val j.val).trans_lt (Order.lt_succ _)
    exact ⟨k, hjk, (hpq k).resolve_left (hi k hik)⟩

end Posets
