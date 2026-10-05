import Mathlib.SetTheory.Ordinal.Arithmetic

/-! Order-type bounds for monotone maps.  The source is embedded in the
lexicographic product of the target and a uniform bound for its fibers. -/

noncomputable section
open Set
universe u
namespace Posets

theorem ordinal_type_Iio (α : Ordinal.{u}) :
    Ordinal.type (· < · : Iio α → _ → Prop) = Ordinal.lift.{u+1} α := by
  exact Ordinal.typein_ordinal α

theorem ordinal_type_Iic (α : Ordinal.{u}) :
    Ordinal.type (· < · : Iic α → _ → Prop) = Ordinal.lift.{u+1} (Order.succ α) := by
  let e : (· < · : Iic α → _ → Prop) ≃r
      (· < · : Iio (Order.succ α) → _ → Prop) :=
    { toEquiv :=
        { toFun := fun x : Iic α => ⟨x.val, by
            exact (Order.lt_succ_iff (a := x.val) (b := α)).mpr x.property⟩
          invFun := fun x : Iio (Order.succ α) => ⟨x.val, by
            exact (Order.lt_succ_iff (a := x.val) (b := α)).mp x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  exact e.ordinal_type_eq.trans (ordinal_type_Iio _)

theorem ordinal_type_le_mul_of_monotone_fibers
    {X Y : Type u} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y]
    (f : X → Y) (hf : Monotone f) (α : Ordinal.{u})
    (hα : ∀ y, Ordinal.type (· < · : {x : X // f x = y} → _ → Prop) ≤ α) :
    Ordinal.type (· < · : X → _ → Prop) ≤
      α * Ordinal.type (· < · : Y → _ → Prop) := by
  let e (y : Y) : (· < · : {x : X // f x = y} → _ → Prop) ↪r
      (· < · : α.toType → _ → Prop) :=
    Classical.choice (Ordinal.type_le_iff'.mp (by
      simpa only [Ordinal.type_toType] using hα y))
  let g (x : X) : Y × α.toType := (f x, e (f x) ⟨x, rfl⟩)
  have hg : ∀ x x', x < x' → Prod.Lex (· < ·) (· < ·) (g x) (g x') := by
    intro x x' hxx'
    rcases lt_or_eq_of_le (hf hxx'.le) with hlt | heq
    · exact Prod.Lex.left _ _ hlt
    · change Prod.Lex (· < ·) (· < ·)
        (f x, e (f x) ⟨x, rfl⟩) (f x', e (f x') ⟨x', rfl⟩)
      have he : e (f x') ⟨x, heq⟩ < e (f x') ⟨x', rfl⟩ :=
        (e (f x')).map_rel_iff.mpr hxx'
      have hcast (y : Y) (hy : f x = y) :
          e (f x) ⟨x, rfl⟩ = e y ⟨x, hy⟩ := by
        subst y
        rfl
      rw [hcast (f x') heq]
      rw [heq]
      exact Prod.Lex.right (f x') he
  have h := (RelEmbedding.ofMonotone g hg).ordinal_type_le
  simpa only [Ordinal.type_prod_lex, Ordinal.type_toType] using h

end Posets
