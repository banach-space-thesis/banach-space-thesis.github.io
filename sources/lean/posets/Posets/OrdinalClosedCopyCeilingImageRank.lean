import Posets.OrdinalClosedCopyCeilingFibers
import ThesisCommon.Analysis.OrdinalCopiesClassification

/-! Projecting a compact ordinal core through a lower arithmetic level
retains the ordinal rank left after the fiber bound. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinal_type_Icc_zero (α : Ordinal.{u}) :
    Ordinal.type (· < · : OrdinalInterval α → _ → Prop) =
      Ordinal.lift.{u+1} (Order.succ α) := by
  let e : (· < · : OrdinalInterval α → _ → Prop) ≃r (· < · : Iic α → _ → Prop) :=
    { toEquiv :=
        { toFun := fun x => ⟨x.val, x.property.2⟩
          invFun := fun x => ⟨x.val, Ordinal.zero_le _, x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  exact e.ordinal_type_eq.trans (ordinal_type_Iic α)

theorem ordinal_type_compact_order_model {F : Set Ordinal.{u}} {β : Ordinal.{u}}
    (e : OrdinalInterval β ≃ₜ F) (he : StrictMono (fun x => (e x).val)) :
    Ordinal.type (· < · : F → _ → Prop) = Ordinal.lift.{u+1} (Order.succ β) := by
  let r : (· < · : OrdinalInterval β → _ → Prop) ≃r (· < · : F → _ → Prop) :=
    { toEquiv := e.toEquiv
      map_rel_iff' := he.lt_iff_lt }
  exact r.ordinal_type_eq.symm.trans (ordinal_type_Icc_zero β)

theorem ordinalCeiling_image_model_rank
    {A F : Set Ordinal.{u}} {θ a b : Ordinal.{u}}
    (hA : IsCompact A) (hθ : θ ∈ A)
    (hgrid : ∀ q : Ordinal.{u}, q ≠ 0 → Ordinal.omega0 ^ a * q ≤ θ →
      Ordinal.omega0 ^ a * q ∈ A)
    (hF : IsCompact F) (hFθ : F ⊆ Iic θ) (hb : b ≠ 0)
    (hrank : (ordinalDerived F (Order.succ a + b)).Nonempty) :
    ∃ β : Ordinal.{u}, ∃ e : OrdinalInterval β ≃ₜ (ordinalCeiling A '' F),
      StrictMono (fun x => (e x).val) ∧ Ordinal.omega0 ^ b ≤ β := by
  have hne : F.Nonempty := by
    have hs := ordinalDerived_antitone hF.isClosed (Ordinal.zero_le (Order.succ a + b))
    simpa only [ordinalDerived_zero] using hrank.mono hs
  have hQ : IsCompact (ordinalCeiling A '' F) :=
    hF.image (ordinalCeiling_continuous hA ⟨θ, hθ⟩)
  obtain ⟨β, e, he, _⟩ := ordinal_compact_order_homeomorph hQ (hne.image _)
  refine ⟨β, e, he, ?_⟩
  by_contra hnot
  have hβ : β < Ordinal.omega0 ^ b := lt_of_not_ge hnot
  obtain ⟨η, d, hd, _⟩ := ordinal_compact_order_homeomorph hF hne
  have hη : Ordinal.omega0 ^ (Order.succ a + b) ≤ η :=
    ordinal_power_le_compact_model d
      (ne_of_gt ((Ordinal.succ_pos a).trans_le (Ordinal.le_add_right _ _))) hrank
  have htype := ordinalCeiling_image_type_bound hA hθ
    (Ordinal.opow_ne_zero a Ordinal.omega0_ne_zero) hgrid hFθ
  rw [ordinal_type_compact_order_model d hd, ordinal_type_compact_order_model e he,
    ← Ordinal.lift_mul] at htype
  have hbound : Order.succ η ≤ Order.succ (Ordinal.omega0 ^ a) * Order.succ β :=
    Ordinal.lift_le.mp htype
  have hδ : Order.succ (Ordinal.omega0 ^ a) ≤ Ordinal.omega0 ^ Order.succ a :=
    Order.succ_le_iff.mpr ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      (Order.lt_succ a))
  have hβs : Order.succ β < Ordinal.omega0 ^ b :=
    (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hb).succ_lt hβ
  have hsmall : Order.succ η < Ordinal.omega0 ^ (Order.succ a + b) := calc
    Order.succ η ≤ Order.succ (Ordinal.omega0 ^ a) * Order.succ β := hbound
    _ ≤ Ordinal.omega0 ^ Order.succ a * Order.succ β := mul_le_mul_right' hδ _
    _ < Ordinal.omega0 ^ Order.succ a * Ordinal.omega0 ^ b :=
      mul_lt_mul_of_pos_left hβs (Ordinal.opow_pos _ Ordinal.omega0_pos)
    _ = Ordinal.omega0 ^ (Order.succ a + b) := (Ordinal.opow_add _ _ _).symm
  exact hsmall.not_ge (hη.trans (Order.le_succ η))

end Posets
