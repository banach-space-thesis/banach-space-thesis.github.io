import Posets.OrdinalClosedCopyPacketLift
import Posets.OrdinalClosedCopyCeilingImageRank

/-! A sufficiently large ordinal core has a large intersection with one
actual upper ceiling fiber.  The proof groups arithmetic ceiling indices
into packets of regular-cardinal length. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalCeiling_exists_large_upper_fiber
    {c : Cardinal.{u}} (hc : c.IsRegular) (n : ℕ)
    {A F : Set Ordinal.{u}} {θ β : Ordinal.{u}}
    (hA : IsCompact A) (hθ : θ ∈ A)
    (hdiv : ∀ y ∈ A, c.ord ^ (n + 1 : Ordinal) ∣ y)
    (hθbound : θ ≤ c.ord ^ (n + 1 : Ordinal) * (c.ord * β))
    (hF : F ⊆ Iic θ)
    (hlarge : Ordinal.lift.{u+1} (c.ord ^ (n + 1 : Ordinal) * Order.succ β) <
      Ordinal.type (· < · : F → _ → Prop)) :
    ∃ y : Ordinal.{u}, Ordinal.lift.{u+1} (c.ord ^ (n + 1 : Ordinal)) ≤
      Ordinal.type (· < · : (F ∩ {x | ordinalCeiling A x = y} : Set Ordinal.{u}) → _ → Prop) := by
  classical
  let δ := c.ord ^ (n + 1 : Ordinal)
  have hδ : δ ≠ 0 := (Ordinal.opow_pos _ hc.ord_pos).ne'
  let f (x : F) : Ordinal.{u} := ordinalCeiling A x / δ
  have hf : Monotone f := fun x x' h =>
    Ordinal.div_le_left (ordinalCeiling_mono hA ⟨θ, hθ⟩ h) δ
  have hb (x : F) : f x < c.ord * Order.succ β := by
    have hy : ordinalCeiling A x ≤ θ := ordinalCeiling_le_of_mem hθ (hF x.property)
    exact (Ordinal.div_le_of_le_mul (hy.trans hθbound)).trans_lt
      (mul_lt_mul_of_pos_left (Order.lt_succ β) hc.ord_pos)
  by_contra hn
  have hsmall (y : Ordinal.{u}) :
      Ordinal.type (· < · : {x : F // f x = y} → _ → Prop) <
        Ordinal.lift.{u+1} δ := by
    have htarget : Ordinal.type
        (· < · : (F ∩ {x | ordinalCeiling A x = δ * y} : Set Ordinal.{u}) → _ → Prop) <
          Ordinal.lift.{u+1} δ := lt_of_not_ge (fun h => hn ⟨δ * y, h⟩)
    let e (x : {x : F // f x = y}) :
        (F ∩ {x | ordinalCeiling A x = δ * y} : Set Ordinal.{u}) :=
      ⟨x.val.val, x.val.property, by
        have hd := Ordinal.div_mul_cancel hδ
          (hdiv _ (ordinalCeiling_mem hA ⟨θ, hθ⟩ x.val.val))
        exact hd.symm.trans (congrArg (fun z => δ * z) x.property)⟩
    have he : StrictMono e := fun _ _ h => h
    exact (RelEmbedding.ofMonotone e he).ordinal_type_le.trans_lt htarget
  exact hlarge.not_ge (ordinal_type_le_of_regular_packets_lift hc n f hf
    (Order.succ β) hb hsmall)

theorem ordinal_compact_type_succ_lower_of_limit
    {C : Set Ordinal.{u}} (hC : IsCompact C) {δ : Ordinal.{u}}
    (hδ : IsSuccLimit δ)
    (htype : Ordinal.lift.{u+1} δ ≤ Ordinal.type (· < · : C → _ → Prop)) :
    Ordinal.lift.{u+1} (Order.succ δ) ≤ Ordinal.type (· < · : C → _ → Prop) := by
  classical
  have hne : C.Nonempty := by
    by_contra hn
    letI : IsEmpty C := ⟨fun x => hn ⟨x.val, x.property⟩⟩
    rw [Ordinal.type_eq_zero_iff_isEmpty.mpr inferInstance] at htype
    have hz : 0 < Ordinal.lift.{u+1} δ := by
      have h : Ordinal.lift.{u+1} (0 : Ordinal.{u}) < Ordinal.lift.{u+1} δ :=
        Ordinal.lift_lt.mpr (show (0 : Ordinal.{u}) < δ from hδ.bot_lt)
      simpa only [Ordinal.lift_zero] using h
    exact hz.not_ge htype
  obtain ⟨η, e, he, _⟩ := ordinal_compact_order_homeomorph hC hne
  rw [ordinal_type_compact_order_model e he] at htype ⊢
  apply Ordinal.lift_le.mpr
  apply Order.succ_le_succ
  by_contra hnot
  exact (hδ.succ_lt (lt_of_not_ge hnot)).not_ge (Ordinal.lift_le.mp htype)

end Posets
