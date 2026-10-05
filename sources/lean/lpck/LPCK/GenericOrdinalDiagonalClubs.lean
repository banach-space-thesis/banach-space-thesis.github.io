/- Universe-polymorphic extension of Posets.OrdinalIdealTransportDiagonalClubs. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalSmallFamilies

/-! A diagonal intersection of closed cofinal sets is cofinal below a
regular uncountable initial ordinal. This is the large-family counterpart
of the small-family club intersection used in block compression. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
set_option synthInstance.maxHeartbeats 200000
open JLMS
set_option maxHeartbeats 800000

def ordinalDiagonalIntersection (κ : Ordinal.{u}) (s : Ordinal.{u} → Set Ordinal.{u}) :
    Set Ordinal.{u} := {δ | ∀ i < κ, i < δ → δ ∈ s i}

theorem isClosed_ordinalDiagonalIntersection
    (κ : Ordinal.{u}) (s : Ordinal.{u} → Set Ordinal.{u})
    (hs : ∀ i < κ, IsClosed (s i)) : IsClosed (ordinalDiagonalIntersection κ s) := by
  have he : ordinalDiagonalIntersection κ s = ⋂ i : Set.Iio κ, (Set.Iic i.val ∪ s i.val) := by
    ext δ
    simp only [ordinalDiagonalIntersection, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_union, Set.mem_Iic, Subtype.forall]
    constructor
    · intro h i hi
      by_cases hid : i < δ
      · exact Or.inr (h i hi hid)
      · exact Or.inl (le_of_not_gt hid)
    · intro h i hi hid
      exact (h i hi).resolve_left (not_le_of_gt hid)
  rw [he]
  exact isClosed_iInter (fun i => isClosed_Iic.union (hs i.val i.property))

theorem exists_regularOrdinal_diagonalIntersection_above
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (s : Ordinal.{u} → Set Ordinal.{u}) (hclosed : ∀ i < c.ord, IsClosed (s i))
    (hcofinal : ∀ i < c.ord, ∀ β < c.ord, ∃ δ < c.ord, β < δ ∧ δ ∈ s i)
    (β : Ordinal.{u}) (hβ : β < c.ord) :
    ∃ δ < c.ord, β < δ ∧ δ ∈ ordinalDiagonalIntersection c.ord s := by
  have hsmall (a : Set.Ioo (0 : Ordinal.{u}) c.ord) :
      ∃ δ < c.ord, a.val < δ ∧ ∀ i < a.val, δ ∈ s i := by
    letI : Nonempty a.val.toType := ⟨Ordinal.enumIsoToType a.val ⟨0, a.property.1⟩⟩
    have hi : Cardinal.mk a.val.toType < c.ord.cof := by
      simpa only [Cardinal.mk_toType, hc.cof_eq] using Cardinal.lt_ord.mp a.property.2
    obtain ⟨δ, hδ, haδ, hs⟩ := exists_smallIndex_closed_ordinal_above
      (by simpa only [hc.cof_eq] using hu) hi
      (fun i : a.val.toType => s ((Ordinal.enumIsoToType a.val).symm i).val)
      (fun i => hclosed _ (((Ordinal.enumIsoToType a.val).symm i).property.trans a.property.2))
      (fun i => hcofinal _ (((Ordinal.enumIsoToType a.val).symm i).property.trans a.property.2))
      a.val a.property.2
    refine ⟨δ, hδ, haδ, ?_⟩
    intro i hi
    simpa only [OrderIso.symm_apply_apply] using hs (Ordinal.enumIsoToType a.val ⟨i, hi⟩)
  let next (a : Set.Ioo (0 : Ordinal.{u}) c.ord) : Set.Ioo (0 : Ordinal.{u}) c.ord :=
    ⟨Classical.choose (hsmall a), a.property.1.trans (Classical.choose_spec (hsmall a)).2.1,
      (Classical.choose_spec (hsmall a)).1⟩
  have hnext (a : Set.Ioo (0 : Ordinal.{u}) c.ord) : a.val < (next a).val ∧
      ∀ i < a.val, (next a).val ∈ s i := (Classical.choose_spec (hsmall a)).2
  let start : Set.Ioo (0 : Ordinal.{u}) c.ord :=
    ⟨Order.succ β, (Ordinal.zero_le β).trans_lt (Order.lt_succ β),
      (Cardinal.isSuccLimit_ord hu.le).succ_lt hβ⟩
  let a (n : ℕ) := next^[n] start
  let b (n : ℕ) := (a n).val
  have hstep (n : ℕ) : a (n+1) = next (a n) := Function.iterate_succ_apply' next n start
  have hmono : StrictMono b := strictMono_nat_of_lt_succ (fun n => by
    change (a n).val < (a (n+1)).val
    rw [hstep]
    exact (hnext (a n)).1)
  let δ := ⨆ n, b n
  have hδ : δ < c.ord := Ordinal.iSup_lt_ord_lift
    (by simpa only [hc.cof_eq] using hu) (fun n => (a n).property.2)
  have hβδ : β < δ := (Order.lt_succ β).trans_le
    (by simpa only [b, a, Function.iterate_zero_apply, start] using Ordinal.le_iSup b 0)
  refine ⟨δ, hδ, hβδ, ?_⟩
  intro i hiκ hiδ
  obtain ⟨N, hN⟩ := Ordinal.lt_iSup_iff.mp hiδ
  have heq : (⨆ n : ℕ, b (n + N + 1)) = δ := by
    apply le_antisymm
    · apply Ordinal.iSup_le
      intro n
      exact Ordinal.le_iSup b _
    · apply Ordinal.iSup_le
      intro n
      exact (hmono.monotone (by omega : n ≤ n + N + 1)).trans
        (Ordinal.le_iSup (fun n => b (n+N+1)) n)
  rw [← heq]
  apply (hclosed i hiκ).closure_subset
  apply closure_mono (t := s i) ?_
    (csSup_mem_closure (Set.range_nonempty _) (Ordinal.bddAbove_range _))
  rintro _ ⟨n, rfl⟩
  change (a (n+N+1)).val ∈ s i
  rw [hstep]
  exact (hnext (a (n+N))).2 i (hN.trans_le (hmono.monotone (Nat.le_add_left N n)))

end LPCK.GenericOrdinal



