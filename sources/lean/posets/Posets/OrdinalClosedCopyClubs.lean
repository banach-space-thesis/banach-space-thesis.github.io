import Posets.OrdinalClosedCopyBlockwise
import JLMS.OrdinalClosedIntersections

/-! Closed ordinal copies with an independently prescribed club in each
bottom block.  The block junctions are fixed and the whole map is continuous. -/

noncomputable section
namespace Posets
open JLMS
universe u

def ordinalClubSelector (κ : Ordinal.{u}) (s : Set Ordinal.{u}) :
    Ordinal.{u} → Ordinal.{u} := Ordinal.enumOrd (insert 0 s ∪ Set.Ici κ)

private theorem ordinalClubSelector_unbounded (κ : Ordinal.{u}) (s : Set Ordinal.{u}) :
    ¬ BddAbove (insert 0 s ∪ Set.Ici κ) := by
  rw [not_bddAbove_iff]
  intro a
  exact ⟨max κ (Order.succ a), Or.inr (show κ ≤ max κ (Order.succ a) from le_max_left _ _),
    (Order.lt_succ a).trans_le (le_max_right _ _)⟩

theorem ordinalClubSelector_isNormal (κ : Ordinal.{u}) {s : Set Ordinal.{u}}
    (hs : IsClosed s) : Ordinal.IsNormal (ordinalClubSelector κ s) :=
  (Ordinal.enumOrd_isNormal_iff_isClosed (ordinalClubSelector_unbounded κ s)).mpr
    ((isClosed_singleton.union hs).union isClosed_Ici)

@[simp] theorem ordinalClubSelector_zero (κ : Ordinal.{u}) (s : Set Ordinal.{u}) :
    ordinalClubSelector κ s 0 = 0 := by
  apply le_antisymm _ (Ordinal.zero_le _)
  exact Ordinal.enumOrd_le_of_forall_lt (Or.inl (Set.mem_insert _ _))
    (fun b hb => (Ordinal.not_lt_zero b hb).elim)

theorem ordinalClubSelector_lt {c : Cardinal.{u}} (hc : c.IsRegular)
    {s : Set Ordinal.{u}}
    (hcofinal : ∀ β < c.ord, ∃ δ < c.ord, β < δ ∧ δ ∈ s)
    {ν : Ordinal.{u}} (hν : ν < c.ord) : ordinalClubSelector c.ord s ν < c.ord := by
  apply enumOrd_lt_of_cofinal_below
    (fun ξ hξ => by simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hξ) _ ν hν
  intro β hβ
  obtain ⟨δ, hδ, hβδ, hδs⟩ := hcofinal β hβ
  exact ⟨δ, hδ, hβδ, Or.inl (Set.mem_insert_of_mem 0 hδs)⟩

@[simp] theorem ordinalClubSelector_endpoint {c : Cardinal.{u}} (hc : c.IsRegular)
    {s : Set Ordinal.{u}} (hs : IsClosed s)
    (hcofinal : ∀ β < c.ord, ∃ δ < c.ord, β < δ ∧ δ ∈ s) :
    ordinalClubSelector c.ord s c.ord = c.ord := by
  apply le_antisymm _ (ordinalClubSelector_isNormal c.ord hs).le_apply
  exact Ordinal.enumOrd_le_of_forall_lt (Or.inr (show c.ord ≤ c.ord from le_rfl))
    (fun ν hν => ordinalClubSelector_lt hc hcofinal hν)

theorem ordinalClubSelector_mem {c : Cardinal.{u}} (hc : c.IsRegular)
    {s : Set Ordinal.{u}} (hs : IsClosed s)
    (hcofinal : ∀ β < c.ord, ∃ δ < c.ord, β < δ ∧ δ ∈ s)
    {ν : Ordinal.{u}} (hνzero : 0 < ν) (hν : ν < c.ord) :
    ordinalClubSelector c.ord s ν ∈ s := by
  have hm := Ordinal.enumOrd_mem (ordinalClubSelector_unbounded c.ord s) ν
  have hlt := ordinalClubSelector_lt hc hcofinal hν
  have hpos : 0 < ordinalClubSelector c.ord s ν := by
    simpa only [ordinalClubSelector_zero] using
      (ordinalClubSelector_isNormal c.ord hs).strictMono hνzero
  rcases hm with hm | hm
  · exact (Set.mem_insert_iff.mp hm).resolve_left (ne_of_gt hpos)
  · exact (not_le_of_gt hlt hm).elim

def ordinalClosedCopyFromClubs {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (s : Ordinal.{u} → Set Ordinal.{u}) (hs : ∀ q, IsClosed (s q))
    (hcofinal : ∀ q β, β < c.ord → ∃ δ < c.ord, β < δ ∧ δ ∈ s q) :
    C(OrdinalInterval (c.ord * η), OrdinalInterval (c.ord * η)) :=
  ordinalBlockwiseContinuousMap (by
    have h : Ordinal.omega0 ≤ c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
    exact (Ordinal.omega0_pos.trans_le h).ne') η
    (fun q => ordinalClubSelector c.ord (s q))
    (fun q => ordinalClubSelector_isNormal c.ord (hs q))
    (fun q => ordinalClubSelector_zero c.ord (s q))
    (fun q => ordinalClubSelector_endpoint hc (hs q) (hcofinal q))

theorem ordinalClosedCopyFromClubs_strictMono {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (s : Ordinal.{u} → Set Ordinal.{u}) (hs : ∀ q, IsClosed (s q))
    (hcofinal : ∀ q β, β < c.ord → ∃ δ < c.ord, β < δ ∧ δ ∈ s q) :
    StrictMono (ordinalClosedCopyFromClubs hc hu η s hs hcofinal) :=
  ordinalBlockwiseContinuousMap_strictMono _ _ _ _ _ _

theorem ordinalClosedCopyFromClubs_range_closed {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (s : Ordinal.{u} → Set Ordinal.{u}) (hs : ∀ q, IsClosed (s q))
    (hcofinal : ∀ q β, β < c.ord → ∃ δ < c.ord, β < δ ∧ δ ∈ s q) :
    IsClosed (Set.range (ordinalClosedCopyFromClubs hc hu η s hs hcofinal)) :=
  ordinalBlockwiseContinuousMap_range_closed _ _ _ _ _ _

theorem ordinalClosedCopyFromClubs_junction {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (s : Ordinal.{u} → Set Ordinal.{u}) (hs : ∀ q, IsClosed (s q))
    (hcofinal : ∀ q β, β < c.ord → ∃ δ < c.ord, β < δ ∧ δ ∈ s q)
    (q : Ordinal.{u}) (hq : q ≤ η) :
    ordinalClosedCopyFromClubs hc hu η s hs hcofinal
      ⟨c.ord * q, Ordinal.zero_le _, mul_le_mul_left' hq _⟩ =
      ⟨c.ord * q, Ordinal.zero_le _, mul_le_mul_left' hq _⟩ :=
  Subtype.ext (ordinalBlockwiseSelector_junction (by
    have h : Ordinal.omega0 ≤ c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
    exact (Ordinal.omega0_pos.trans_le h).ne') _
    (fun q => ordinalClubSelector_zero c.ord (s q)) q)

theorem ordinalClosedCopyFromClubs_mem {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (s : Ordinal.{u} → Set Ordinal.{u}) (hs : ∀ q, IsClosed (s q))
    (hcofinal : ∀ q β, β < c.ord → ∃ δ < c.ord, β < δ ∧ δ ∈ s q)
    (x : OrdinalInterval (c.ord * η)) (hx : x.val % c.ord ≠ 0) :
    (ordinalClosedCopyFromClubs hc hu η s hs hcofinal x).val % c.ord ∈ s (x.val / c.ord) := by
  have hκ : c.ord ≠ 0 := by
    have h : Ordinal.omega0 ≤ c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
    exact (Ordinal.omega0_pos.trans_le h).ne'
  have hr := Ordinal.mod_lt x.val hκ
  have hlt := ordinalClubSelector_lt hc (hcofinal (x.val / c.ord)) hr
  change (c.ord * (x.val / c.ord) +
    ordinalClubSelector c.ord (s (x.val / c.ord)) (x.val % c.ord)) % c.ord ∈ _
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlt]
  exact ordinalClubSelector_mem hc (hs _) (hcofinal _)
    (Ordinal.pos_iff_ne_zero.mpr hx) hr

theorem ordinalClosedCopyFromClubs_quotient {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (s : Ordinal.{u} → Set Ordinal.{u}) (hs : ∀ q, IsClosed (s q))
    (hcofinal : ∀ q β, β < c.ord → ∃ δ < c.ord, β < δ ∧ δ ∈ s q)
    (x : OrdinalInterval (c.ord * η)) :
    (ordinalClosedCopyFromClubs hc hu η s hs hcofinal x).val / c.ord = x.val / c.ord := by
  have hκ : c.ord ≠ 0 := by
    have h : Ordinal.omega0 ≤ c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
    exact (Ordinal.omega0_pos.trans_le h).ne'
  have hlt := ordinalClubSelector_lt hc (hcofinal (x.val / c.ord)) (Ordinal.mod_lt x.val hκ)
  change (c.ord * (x.val / c.ord) +
    ordinalClubSelector c.ord (s (x.val / c.ord)) (x.val % c.ord)) / c.ord = _
  rw [Ordinal.mul_add_div _ hκ, Ordinal.div_eq_zero_of_lt hlt, add_zero]

end Posets
