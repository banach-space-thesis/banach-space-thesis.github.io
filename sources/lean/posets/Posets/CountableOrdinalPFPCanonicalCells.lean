import Posets.CountableOrdinalPFPRetractions
import ThesisCommon.Analysis.OrdinalScattered

/-! Canonical isolated cells occur arbitrarily close below every accumulation
point of a compact ordinal level. Their entire fibers can be placed above a
prescribed bound, which will give disjoint children even at limit ranks. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalCeiling_succ_lt_of_mem_derivedSet {A : Set Ordinal.{u}}
    {x a : Ordinal.{u}} (hx : x ∈ derivedSet A) (ha : a < x) :
    ordinalCeiling A (succ a) < x := by
  have hacc : x.IsAcc A := hx
  obtain ⟨b, hbA, hab, hbx⟩ := hacc.forall_lt a ha
  exact (ordinalCeiling_le_of_mem hbA (succ_le_iff.mpr hab)).trans_lt hbx

theorem ordinalCeiling_succ_gt {A : Set Ordinal.{u}} (hA : IsCompact A)
    {x a : Ordinal.{u}} (hx : x ∈ derivedSet A) (ha : a < x) :
    a < ordinalCeiling A (succ a) := by
  have hxA : x ∈ A := (isClosed_iff_derivedSet_subset A).mp hA.isClosed hx
  exact (lt_succ a).trans_le (le_ordinalCeiling hA ⟨x, hxA⟩
    ((succ_le_iff.mpr ha).trans (le_csSup hA.bddAbove hxA)))

theorem ordinalTowerCell_succ_ceiling_bounds (θ : Ordinal.{u})
    {A : Set Ordinal.{u}} (hA : IsCompact A) (hθ : θ ∈ A)
    {x a : Ordinal.{u}} (hx : x ∈ derivedSet A) (ha : a < x) (haA : a ∈ A)
    {z : Iic θ} (hz : z ∈ ordinalTowerCell θ A (ordinalCeiling A (succ a))) :
    a < z.val ∧ z.val ≤ ordinalCeiling A (succ a) := by
  have hza : ordinalCeiling A z = ordinalCeiling A (succ a) := hz
  constructor
  · by_contra h
    have hle := ordinalCeiling_le_of_mem haA (le_of_not_gt h)
    rw [hza] at hle
    exact (ordinalCeiling_succ_gt hA hx ha).not_ge hle
  · rw [← hza]
    exact le_ordinalCeiling hA ⟨θ, hθ⟩ (z.property.trans (le_csSup hA.bddAbove hθ))

theorem ordinal_exists_isolated_cell_above (θ : Ordinal.{u})
    {A : Set Ordinal.{u}} (hA : IsCompact A) (hθ : θ ∈ A)
    {x b : Ordinal.{u}} (hx : x ∈ derivedSet A) (hb : b < x) :
    ∃ y : A, b < y.val ∧ y.val < x ∧ IsOpen ({y} : Set A) ∧
      ∀ z ∈ ordinalTowerCell θ A y, b < z.val ∧ z.val ≤ y.val := by
  have hacc : x.IsAcc A := hx
  obtain ⟨a, haA, hba, hax⟩ := hacc.forall_lt b hb
  have hxA : x ∈ A := (isClosed_iff_derivedSet_subset A).mp hA.isClosed hx
  let y : A := ⟨ordinalCeiling A (succ a), ordinalCeiling_mem hA ⟨θ, hθ⟩ _⟩
  refine ⟨y, hba.trans (ordinalCeiling_succ_gt hA hx hax),
    ordinalCeiling_succ_lt_of_mem_derivedSet hx hax, ?_, ?_⟩
  · apply ordinalCeiling_isolated_of_isOpen_Ici hA ⟨θ, hθ⟩
      ((succ_le_iff.mpr hax).trans (le_csSup hA.bddAbove hxA))
    rw [Order.Ici_succ]
    exact isOpen_Ioi
  · intro z hz
    obtain ⟨haz, hzy⟩ := ordinalTowerCell_succ_ceiling_bounds θ hA hθ hx hax haA hz
    exact ⟨hba.trans haz, hzy⟩

end Posets
