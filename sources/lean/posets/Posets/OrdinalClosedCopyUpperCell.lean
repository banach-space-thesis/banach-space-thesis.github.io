import Posets.OrdinalClosedCopyUpperCore
import Posets.OrdinalClosedCopyTowerImage
import Posets.OrdinalClosedCoreOrder

/-! A large compact core inside one ceiling fiber forces that fiber to be
an actual clopen tower cell, including at uncountable ordinal junctions. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalCeiling_isolated_of_compact_large_fiber
    {A C : Set Ordinal.{u}} {θ y δ : Ordinal.{u}}
    (hA : IsCompact A) (hθ : θ ∈ A)
    (hC : IsCompact C) (hCθ : C ⊆ Iic θ)
    (hCy : ∀ x ∈ C, ordinalCeiling A x = y)
    (hδ : IsSuccLimit δ)
    (htype : Ordinal.lift.{u+1} (Order.succ δ) ≤
      Ordinal.type (· < · : C → _ → Prop)) :
    ∃ hy : y ∈ A, IsOpen ({⟨y, hy⟩} : Set A) := by
  classical
  have hne : C.Nonempty := by
    by_contra hn
    letI : IsEmpty C := ⟨fun x => hn ⟨x.val, x.property⟩⟩
    rw [Ordinal.type_eq_zero_iff_isEmpty.mpr inferInstance] at htype
    exact (show 0 < Ordinal.lift.{u+1} (Order.succ δ) by
      simpa only [Ordinal.lift_zero] using Ordinal.lift_lt.mpr (Ordinal.succ_pos δ)).not_ge htype
  obtain ⟨η, e, he, _⟩ := ordinal_compact_order_homeomorph hC hne
  rw [ordinal_type_compact_order_model e he] at htype
  have hδη : δ ≤ η := Order.succ_le_succ_iff.mp (Ordinal.lift_le.mp htype)
  have h1η : (1 : Ordinal.{u}) ≤ η := (Ordinal.one_lt_of_isSuccLimit hδ).le.trans hδη
  let z₀ : C := e ⟨0, Ordinal.zero_le _, Ordinal.zero_le _⟩
  let z₁ : C := e ⟨1, Ordinal.zero_le _, h1η⟩
  have hz : z₀.val < z₁.val := he (show (0 : Ordinal.{u}) < 1 from zero_lt_one)
  have hy : y ∈ A := by
    rw [← hCy z₀.val z₀.property]
    exact ordinalCeiling_mem hA ⟨θ, hθ⟩ _
  have hzy : z₀.val < y := by
    have h := le_ordinalCeiling hA ⟨θ, hθ⟩
      ((hCθ z₁.property).trans (le_csSup hA.bddAbove hθ))
    rw [hCy z₁.val z₁.property] at h
    exact hz.trans_le h
  refine ⟨hy, ?_⟩
  have heq : (Subtype.val : A → Ordinal.{u}) ⁻¹' (Ioi z₀.val ∩ Iic y) =
      {⟨y, hy⟩} := by
    ext x
    constructor
    · intro hx
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      apply le_antisymm hx.2
      change y ≤ x.val
      rw [← hCy z₀.val z₀.property]
      exact ordinalCeiling_le_of_mem x.property hx.1.le
    · intro hx
      rw [mem_singleton_iff] at hx
      subst x
      change z₀.val < y ∧ y ≤ y
      exact ⟨hzy, le_rfl⟩
  rw [← heq]
  exact (isOpen_Ioi.inter (ordinal_isClopen_Iic y).isOpen).preimage continuous_subtype_val

theorem ordinalTower_exists_high_upper_cell
    {c : Cardinal.{u}} (hc : c.IsRegular) (n : ℕ)
    {F : Set Ordinal.{u}} {θ β a : Ordinal.{u}}
    (ha : a ≠ 0) (hscale : Ordinal.omega0 ^ a = c.ord ^ (n + 1 : Ordinal))
    (hθ : θ ∈ ordinalTowerLevel θ a)
    (hθbound : θ ≤ c.ord ^ (n + 1 : Ordinal) * (c.ord * β))
    (hF : IsCompact F) (hFθ : F ⊆ Iic θ)
    (hlarge : Ordinal.lift.{u+1} (c.ord ^ (n + 1 : Ordinal) * Order.succ β) <
      Ordinal.type (· < · : F → _ → Prop)) :
    ∃ y : ordinalTowerLevel θ a,
      IsOpen ({y} : Set (ordinalTowerLevel θ a)) ∧
      (ordinalDerived (F ∩ {x | ordinalCeiling (ordinalTowerLevel θ a) x = y.val}) a).Nonempty := by
  have hA := ordinalTowerLevel_isCompact θ a
  have hd (y : Ordinal.{u}) (hy : y ∈ ordinalTowerLevel θ a) :
      c.ord ^ (n + 1 : Ordinal) ∣ y := by
    rw [ordinalTowerLevel, ordinalDerived_Iic, ordinalDerived_univ, if_neg ha] at hy
    rw [← hscale]
    exact hy.1.2
  obtain ⟨y, hy⟩ := ordinalCeiling_exists_large_upper_fiber hc n hA hθ hd hθbound hFθ hlarge
  let C : Set Ordinal.{u} := F ∩ {x | ordinalCeiling (ordinalTowerLevel θ a) x = y}
  have hC : IsCompact C := hF.inter_right
    (isClosed_singleton.preimage (ordinalCeiling_continuous hA ⟨θ, hθ⟩))
  have hδ : IsSuccLimit (c.ord ^ (n + 1 : Ordinal)) :=
    Ordinal.isSuccLimit_opow_left (Cardinal.isSuccLimit_ord hc.aleph0_le)
      (Ordinal.succ_ne_zero (n : Ordinal))
  have ht := ordinal_compact_type_succ_lower_of_limit hC hδ hy
  obtain ⟨hyA, hyo⟩ := ordinalCeiling_isolated_of_compact_large_fiber hA hθ hC
    (fun _ hx => hFθ hx.1) (fun _ hx => hx.2) hδ ht
  refine ⟨⟨y, hyA⟩, hyo, ordinalClosedCore_rank_of_order_type hC ha ?_⟩
  rwa [hscale]

end Posets
