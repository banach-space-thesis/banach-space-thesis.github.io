import Posets.OrdinalClosedCopyPacketBound

/-! Grouping consecutive fibers into packets of regular-cardinal length
improves the uniform order bound by one cardinal power. -/

noncomputable section
open Set
universe u
namespace Posets

theorem ordinal_mod_mono_of_div_eq {a b κ : Ordinal.{u}}
    (hab : a ≤ b) (he : a / κ = b / κ) : a % κ ≤ b % κ := by
  have h := hab
  rw [← Ordinal.div_add_mod a κ, ← Ordinal.div_add_mod b κ, he] at h
  exact (add_le_add_iff_left _).mp h

theorem ordinal_type_le_of_regular_packets
    {X : Type u} [LinearOrder X] [WellFoundedLT X]
    {c : Cardinal.{u}} (hc : c.IsRegular) (n : ℕ)
    (f : X → Ordinal.{u}) (hf : Monotone f) (β : Ordinal.{u})
    (hbound : ∀ x, f x < c.ord * β)
    (hF : ∀ y, Ordinal.type (· < · : {x : X // f x = y} → _ → Prop) <
      c.ord ^ (n + 1 : Ordinal)) :
    Ordinal.type (· < · : X → _ → Prop) ≤ c.ord ^ (n + 1 : Ordinal) * β := by
  classical
  have hc0 : c.ord ≠ 0 := hc.ord_pos.ne'
  let g (x : X) : β.toType := Ordinal.enumIsoToType β
    ⟨f x / c.ord, (Ordinal.div_lt hc0).mpr (hbound x)⟩
  have hg : Monotone g := fun x x' h =>
    (Ordinal.enumIsoToType β).monotone (Ordinal.div_le_left (hf h) _)
  have hgf (y : β.toType) :
      Ordinal.type (· < · : {x : X // g x = y} → _ → Prop) ≤
        c.ord ^ (n + 1 : Ordinal) := by
    let Z := {x : X // g x = y}
    let r (x : Z) : c.ord.toType := Ordinal.enumIsoToType c.ord
      ⟨f x.val % c.ord, Ordinal.mod_lt _ hc0⟩
    have hquot (x x' : Z) : f x.val / c.ord = f x'.val / c.ord := by
      have h := congrArg (fun z => ((Ordinal.enumIsoToType β).symm z).val)
        (x.property.trans x'.property.symm)
      simpa only [g, OrderIso.symm_apply_apply] using h
    have hr : Monotone r := fun x x' h => (Ordinal.enumIsoToType c.ord).monotone
      (ordinal_mod_mono_of_div_eq (hf h) (hquot x x'))
    apply ordinal_type_le_of_regular_power_fibers hc n r hr
      (by simpa only [Ordinal.type_toType] using (le_refl c.ord))
    intro z
    let V := {x : Z // r x = z}
    by_cases hn : Nonempty V
    · obtain ⟨x₀⟩ := hn
      have heq (x : V) : f x.val.val = f x₀.val.val := by
        have hm := congrArg (fun z => ((Ordinal.enumIsoToType c.ord).symm z).val)
          (x.property.trans x₀.property.symm)
        have hm' : f x.val.val % c.ord = f x₀.val.val % c.ord := by
          simpa only [r, OrderIso.symm_apply_apply] using hm
        calc f x.val.val = c.ord * (f x.val.val / c.ord) + f x.val.val % c.ord :=
            (Ordinal.div_add_mod _ _).symm
          _ = c.ord * (f x₀.val.val / c.ord) + f x₀.val.val % c.ord := by
            rw [hquot x.val x₀.val, hm']
          _ = f x₀.val.val := Ordinal.div_add_mod _ _
      let e (x : V) : {x : X // f x = f x₀.val.val} := ⟨x.val.val, heq x⟩
      have he : StrictMono e := fun _ _ h => h
      exact (RelEmbedding.ofMonotone e he).ordinal_type_le.trans_lt (hF _)
    · letI : IsEmpty V := not_nonempty_iff.mp hn
      rw [Ordinal.type_eq_zero_iff_isEmpty.mpr inferInstance]
      exact Ordinal.opow_pos _ hc.ord_pos
  have ht := ordinal_type_le_mul_of_monotone_fibers g hg _ hgf
  simpa only [Ordinal.type_toType] using ht

end Posets
