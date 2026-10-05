import Posets.OrdinalClosedCopyFiberTypes
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Principal

/-! Order-type bounds for packets of small ordinal fibers.  The cofinality
condition bounds every proper initial packet, without assuming a uniform
strict bound for the fibers of the full packet. -/

noncomputable section
open Set
universe u
namespace Posets

theorem ordinal_mul_lt_of_small_cof {θ a β : Ordinal.{u}}
    (hθ : Ordinal.Principal (· + ·) θ) (ha : a < θ)
    (hβ : β.card < θ.cof) : a * β < θ := by
  induction β using Ordinal.limitRecOn with
  | zero => simpa using (Ordinal.zero_le a).trans_lt ha
  | succ β ih =>
      rw [Ordinal.mul_succ]
      exact hθ (ih ((Ordinal.card_le_card (Order.le_succ β)).trans_lt hβ)) ha
  | limit β hlim ih =>
      by_cases ha0 : a = 0
      · simpa [ha0] using (Ordinal.zero_le a).trans_lt ha
      rw [← (Ordinal.isNormal_mul_right (Ordinal.pos_iff_ne_zero.mpr ha0)).bsup_eq hlim]
      exact Ordinal.bsup_lt_ord hβ fun b hb =>
        ih b hb ((Ordinal.card_le_card hb.le).trans_lt hβ)

theorem ordinal_type_lt_of_monotone_small_fibers
    {X Y : Type u} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y]
    (f : X → Y) (hf : Monotone f) (θ : Ordinal.{u})
    (hθ : Ordinal.Principal (· + ·) θ)
    (hY : Cardinal.mk Y < θ.cof)
    (hF : ∀ y, Ordinal.type (· < · : {x : X // f x = y} → _ → Prop) < θ) :
    Ordinal.type (· < · : X → _ → Prop) < θ := by
  let μ : Ordinal.{u} := ⨆ y, Ordinal.type (· < · : {x : X // f x = y} → _ → Prop)
  have hμ : μ < θ := Ordinal.iSup_lt_ord hY hF
  have hbound := ordinal_type_le_mul_of_monotone_fibers f hf μ
    (fun y => Ordinal.le_iSup (fun y =>
      Ordinal.type (· < · : {x : X // f x = y} → _ → Prop)) y)
  apply hbound.trans_lt (ordinal_mul_lt_of_small_cof hθ hμ ?_)
  simpa only [Ordinal.card_type] using hY

theorem ordinal_type_le_of_monotone_small_initial_fibers
    {X Y : Type u} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y]
    (f : X → Y) (hf : Monotone f) (θ : Ordinal.{u})
    (hθ : Ordinal.Principal (· + ·) θ)
    (hY : ∀ y : Y, Cardinal.mk (Iic y) < θ.cof)
    (hF : ∀ y, Ordinal.type (· < · : {x : X // f x = y} → _ → Prop) < θ) :
    Ordinal.type (· < · : X → _ → Prop) ≤ θ := by
  have hinit (x : X) : Ordinal.typein (· < · : X → _ → Prop) x < θ := by
    let g : Iio x → Iic (f x) := fun z => ⟨f z.val, hf z.property.le⟩
    have hg : Monotone g := fun _ _ h => hf h
    have hgf (y : Iic (f x)) :
        Ordinal.type (· < · : {z : Iio x // g z = y} → _ → Prop) < θ := by
      let e : {z : Iio x // g z = y} → {z : X // f z = y.val} :=
        fun z => ⟨z.val.val, congrArg Subtype.val z.property⟩
      have he : StrictMono e := fun _ _ h => h
      exact (RelEmbedding.ofMonotone e he).ordinal_type_le.trans_lt (hF y.val)
    exact ordinal_type_lt_of_monotone_small_fibers g hg θ hθ (hY (f x)) hgf
  by_contra hn
  obtain ⟨x, hx⟩ := Ordinal.typein_surj (· < · : X → _ → Prop) (lt_of_not_ge hn)
  exact (hinit x).ne hx

theorem ordinal_regular_finite_power_cof {c : Cardinal.{u}}
    (hc : c.IsRegular) (n : ℕ) : (c.ord ^ (n + 1 : Ordinal)).cof = c := by
  rw [show (n + 1 : Ordinal) = Order.succ (n : Ordinal) from rfl,
    Ordinal.opow_succ]
  exact ((Ordinal.isNormal_mul_right (Ordinal.opow_pos _ hc.ord_pos)).cof_eq
    (Cardinal.isSuccLimit_ord hc.aleph0_le)).trans hc.cof_eq

theorem ordinal_type_le_of_regular_power_fibers
    {X Y : Type u} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y]
    {c : Cardinal.{u}} (hc : c.IsRegular) (n : ℕ)
    (f : X → Y) (hf : Monotone f)
    (hY : Ordinal.type (· < · : Y → _ → Prop) ≤ c.ord)
    (hF : ∀ y, Ordinal.type (· < · : {x : X // f x = y} → _ → Prop) <
      c.ord ^ (n + 1 : Ordinal)) :
    Ordinal.type (· < · : X → _ → Prop) ≤ c.ord ^ (n + 1 : Ordinal) := by
  apply ordinal_type_le_of_monotone_small_initial_fibers f hf _
    (Ordinal.principal_add_opow_of_principal_add
      (Ordinal.principal_add_ord hc.aleph0_le) _) _ hF
  intro y
  rw [ordinal_regular_finite_power_cof hc n]
  have hset : Iic y = insert y (Iio y) := by
    ext z
    simp only [mem_Iic, mem_insert_iff, mem_Iio, le_iff_eq_or_lt]
  rw [hset]
  apply Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt hc.aleph0_le ?_ (hc.nat_lt 1))
  change (Ordinal.typein (· < · : Y → _ → Prop) y).card < c
  exact Cardinal.lt_ord.mp ((Ordinal.typein_lt_type _ y).trans_le hY)

end Posets
