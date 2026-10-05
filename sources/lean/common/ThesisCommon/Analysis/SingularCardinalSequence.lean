import ThesisCommon.Analysis.HajnalCofinality

/-! A cofinal, strictly increasing family of regular cardinals below an
infinite singular cardinal. Its indices are the small type representing the
initial ordinal of the cofinality. -/
noncomputable section
open scoped Cardinal
open Order
namespace ThesisCommon
universe u

theorem exists_cofinal_cardinalFamily (κ : Cardinal.{u}) :
    ∃ f : κ.ord.cof.ord.toType → Cardinal.{u},
      (∀ i, f i < κ) ∧ ∀ c < κ, ∃ i, c ≤ f i := by
  classical
  obtain ⟨ι, g, hg, hι⟩ := Ordinal.exists_lsub_cof κ.ord
  obtain ⟨e⟩ := Cardinal.eq.mp (hι.trans (Cardinal.mk_ord_toType _).symm)
  refine ⟨fun i => (g (e.symm i)).card, ?_, ?_⟩
  · intro i
    apply Cardinal.lt_ord.mp
    simpa only [← hg] using Ordinal.lt_lsub g (e.symm i)
  · intro c hc
    have hco : c.ord < Ordinal.lsub g := by simpa only [hg] using Cardinal.ord_lt_ord.mpr hc
    obtain ⟨i, hi⟩ := Ordinal.lt_lsub_iff.mp hco
    refine ⟨e i, ?_⟩
    simpa only [e.symm_apply_apply, Cardinal.card_ord] using Ordinal.card_le_card hi

theorem succ_lt_of_singular {κ c : Cardinal.{u}}
    (hsing : ¬ κ.IsRegular) (hc : c < κ) (hcInf : Cardinal.aleph0 ≤ c) :
    succ c < κ := by
  refine lt_of_le_of_ne (succ_le_of_lt hc) ?_
  intro heq
  exact hsing (heq ▸ Cardinal.isRegular_succ hcInf)

/-- The sequence is strictly increasing and cofinal; each entry is regular,
lies strictly below κ, and exceeds the specified infinite lower bound ν. -/
theorem exists_regular_cofinal_cardinalSequence (κ ν : Cardinal.{u})
    (hsing : ¬ κ.IsRegular) (hνInf : Cardinal.aleph0 ≤ ν) (hν : ν < κ) :
    ∃ s : κ.ord.cof.ord.toType → Cardinal.{u},
      (∀ i, (s i).IsRegular) ∧ (∀ i, ν < s i) ∧ (∀ i, s i < κ) ∧
      StrictMono s ∧ ∀ c < κ, ∃ i, c < s i := by
  classical
  obtain ⟨f, hf, hcof⟩ := exists_cofinal_cardinalFamily κ
  let I := κ.ord.cof.ord.toType
  let C := {c : Cardinal.{u} // c < κ ∧ c.IsRegular}
  let bound (i : I) (r : ∀ j : I, j < i → C) : Cardinal.{u} :=
    max ν (max (f i) (⨆ j : Set.Iio i, (r j.val j.property).val))
  have hbound (i : I) (r : ∀ j : I, j < i → C) : bound i r < κ := by
    refine max_lt hν (max_lt (hf i) ?_)
    exact Ordinal.iSup_lt (Cardinal.mk_Iio_ord_toType i)
      (fun j => (r j.val j.property).property.1)
  have hboundInf (i : I) (r : ∀ j : I, j < i → C) : Cardinal.aleph0 ≤ bound i r :=
    hνInf.trans (le_max_left _ _)
  let step (i : I) (r : ∀ j : I, j < i → C) : C :=
    ⟨succ (bound i r), succ_lt_of_singular hsing (hbound i r) (hboundInf i r),
      Cardinal.isRegular_succ (hboundInf i r)⟩
  let a : I → C := IsWellFounded.fix ((· < ·) : I → I → Prop) step
  have hrec (i : I) : (a i).val = succ (bound i (fun j _ => a j)) :=
    congrArg Subtype.val (IsWellFounded.fix_eq ((· < ·) : I → I → Prop) step i)
  refine ⟨fun i => (a i).val, fun i => (a i).property.2, ?_,
    fun i => (a i).property.1, ?_, ?_⟩
  · intro i
    change ν < (a i).val
    rw [hrec]
    exact (le_max_left _ _).trans_lt (lt_succ _)
  · intro i j hij
    change (a i).val < (a j).val
    rw [hrec j]
    apply lt_of_le_of_lt ?_ (lt_succ _)
    have hbd : BddAbove (Set.range (fun k : Set.Iio j => (a k.val).val)) :=
      ⟨κ, by rintro _ ⟨k, rfl⟩; exact (a k.val).property.1.le⟩
    exact (le_ciSup hbd ⟨i, hij⟩).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · intro c hc
    obtain ⟨i, hi⟩ := hcof c hc
    refine ⟨i, hi.trans_lt ?_⟩
    change f i < (a i).val
    rw [hrec]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (lt_succ _)

end ThesisCommon
