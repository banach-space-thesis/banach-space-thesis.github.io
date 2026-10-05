import Posets.OrdinalClosedCopyClubs
import JLMS.OrdinalLimitRows

/-! The blockwise club selection can be made at limit indices throughout.
Zero is retained only as the block junction. Every nonzero interior point
then selects a nonzero limit of the prescribed club. -/

noncomputable section
namespace Posets
open JLMS
universe u

def ordinalLimitClubSelector (κ : Ordinal.{u}) (s : Set Ordinal.{u}) (x : Ordinal.{u}) :=
  ordinalClubSelector κ s (Ordinal.omega0 * x)

theorem ordinalLimitClubSelector_isNormal (κ : Ordinal.{u}) {s : Set Ordinal.{u}}
    (hs : IsClosed s) : Ordinal.IsNormal (ordinalLimitClubSelector κ s) :=
  (ordinalClubSelector_isNormal κ hs).comp (Ordinal.isNormal_mul_right Ordinal.omega0_pos)

@[simp] theorem ordinalLimitClubSelector_zero (κ : Ordinal.{u}) (s : Set Ordinal.{u}) :
    ordinalLimitClubSelector κ s 0 = 0 := by simp [ordinalLimitClubSelector]

@[simp] theorem ordinalLimitClubSelector_endpoint {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) {s : Set Ordinal.{u}} (hs : IsClosed s)
    (hcofinal : ∀ β < c.ord, ∃ δ < c.ord, β < δ ∧ δ ∈ s) :
    ordinalLimitClubSelector c.ord s c.ord = c.ord := by
  rw [ordinalLimitClubSelector, initialOrdinal_omega0_mul hu,
    ordinalClubSelector_endpoint hc hs hcofinal]

theorem ordinalLimitClubSelector_lt {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) {s : Set Ordinal.{u}} (hs : IsClosed s)
    (hcofinal : ∀ β < c.ord, ∃ δ < c.ord, β < δ ∧ δ ∈ s)
    {x : Ordinal.{u}} (hx : x < c.ord) : ordinalLimitClubSelector c.ord s x < c.ord := by
  simpa only [ordinalLimitClubSelector_endpoint hc hu hs hcofinal] using
    (ordinalLimitClubSelector_isNormal c.ord hs).strictMono hx

theorem ordinalLimitClubSelector_data {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) {s : Set Ordinal.{u}} (hs : IsClosed s)
    (hcofinal : ∀ β < c.ord, ∃ δ < c.ord, β < δ ∧ δ ∈ s)
    {x : Ordinal.{u}} (hxzero : 0 < x) (hx : x < c.ord) :
    ordinalLimitClubSelector c.ord s x ∈ s ∧
      Order.IsSuccLimit (ordinalLimitClubSelector c.ord s x) ∧
      ordinalClubSelector c.ord s 1 < ordinalLimitClubSelector c.ord s x := by
  have hωx : Ordinal.omega0 * x < c.ord := by
    simpa only [initialOrdinal_omega0_mul hu] using
      (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono hx
  have hlim : Order.IsSuccLimit (Ordinal.omega0 * x) :=
    Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hxzero
  refine ⟨ordinalClubSelector_mem hc hs hcofinal hlim.bot_lt hωx,
    (ordinalClubSelector_isNormal c.ord hs).map_isSuccLimit hlim, ?_⟩
  apply (ordinalClubSelector_isNormal c.ord hs).strictMono
  exact Ordinal.one_lt_omega0.trans_le (by
    simpa only [mul_one] using mul_le_mul_left' (Order.one_le_iff_pos.mpr hxzero) Ordinal.omega0)

def ordinalClosedCopyFromLimitClubs {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (s : Ordinal.{u} → Set Ordinal.{u}) (hs : ∀ q, IsClosed (s q))
    (hcofinal : ∀ q β, β < c.ord → ∃ δ < c.ord, β < δ ∧ δ ∈ s q) :
    C(OrdinalInterval (c.ord * η), OrdinalInterval (c.ord * η)) :=
  ordinalBlockwiseContinuousMap (by
    have h : Ordinal.omega0 ≤ c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
    exact (Ordinal.omega0_pos.trans_le h).ne') η
    (fun q => ordinalLimitClubSelector c.ord (s q))
    (fun q => ordinalLimitClubSelector_isNormal c.ord (hs q))
    (fun q => ordinalLimitClubSelector_zero c.ord (s q))
    (fun q => ordinalLimitClubSelector_endpoint hc hu (hs q) (hcofinal q))

theorem ordinalClosedCopyFromLimitClubs_remainder {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (s : Ordinal.{u} → Set Ordinal.{u}) (hs : ∀ q, IsClosed (s q))
    (hcofinal : ∀ q β, β < c.ord → ∃ δ < c.ord, β < δ ∧ δ ∈ s q)
    (x : OrdinalInterval (c.ord * η)) :
    (ordinalClosedCopyFromLimitClubs hc hu η s hs hcofinal x).val % c.ord =
      ordinalLimitClubSelector c.ord (s (x.val / c.ord)) (x.val % c.ord) := by
  have hκ : c.ord ≠ 0 := by
    have h : Ordinal.omega0 ≤ c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
    exact (Ordinal.omega0_pos.trans_le h).ne'
  have hlt := ordinalLimitClubSelector_lt hc hu (hs (x.val / c.ord))
    (hcofinal (x.val / c.ord)) (Ordinal.mod_lt x.val hκ)
  change (c.ord * (x.val / c.ord) +
    ordinalLimitClubSelector c.ord (s (x.val / c.ord)) (x.val % c.ord)) % c.ord = _
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlt]

end Posets
