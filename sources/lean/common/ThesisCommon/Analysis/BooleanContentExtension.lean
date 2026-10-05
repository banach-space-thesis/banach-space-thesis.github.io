import ThesisCommon.Analysis.BooleanAdjoinNormalForm
import Mathlib.Order.Hom.BoundedLattice

/-! A genuine extension of a Boolean isomorphism by one generator with
matching intersection masses. Strictly positive finite additive contents
prove well-definedness and order reflection of the two-piece normal form. -/
noncomputable section
open Set
namespace ThesisCommon

structure StrictBooleanContent (A : Type*) [BooleanAlgebra A] where
  toFun : A → ℝ
  nonneg : ∀ a, 0 ≤ toFun a
  eq_zero_iff : ∀ a, toFun a = 0 ↔ a = ⊥
  add_disjoint : ∀ a b, Disjoint a b → toFun (a ⊔ b) = toFun a + toFun b

instance strictBooleanContentCoeFun {A : Type*} [BooleanAlgebra A] :
    CoeFun (StrictBooleanContent A) (fun _ => A → ℝ) := ⟨StrictBooleanContent.toFun⟩

variable {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]

theorem StrictBooleanContent.patch (w : StrictBooleanContent A) (a s t : A) :
    w (booleanPatch a s t) = w (s ⊓ a) + w (t ⊓ aᶜ) :=
  w.add_disjoint _ _ (disjoint_compl_right.mono inf_le_right inf_le_right)

theorem StrictBooleanContent.partition (w : StrictBooleanContent A) (a s : A) :
    w s = w (s ⊓ a) + w (s ⊓ aᶜ) := by
  rw [← w.patch, booleanPatch_same]

private theorem cut_le_iff (a s t : A) : s ⊓ a ≤ t ⊓ a ↔ (s ⊓ tᶜ) ⊓ a = ⊥ := by
  rw [le_inf_iff, and_iff_left inf_le_right, ← disjoint_compl_right_iff, disjoint_iff]
  rw [inf_assoc, inf_comm a tᶜ, ← inf_assoc]

variable (wA : StrictBooleanContent A) (wB : StrictBooleanContent B)
  (S : BooleanSubalgebra A) (T : BooleanSubalgebra B) (e : S ≃o T)
  (he : ∀ s : S, wB (e s).val = wA s.val) (a : A) (b : B)
  (hab : ∀ s : S, wB ((e s).val ⊓ b) = wA (s.val ⊓ a))
include he hab

theorem booleanContent_compl_intersection (s : S) :
    wB ((e s).val ⊓ bᶜ) = wA (s.val ⊓ aᶜ) := by
  have hA := wA.partition a s.val
  have hB := wB.partition b (e s).val
  rw [he s, hab s] at hB
  linarith

private theorem matching_cut_le (s t : S) :
    (e s).val ⊓ b ≤ (e t).val ⊓ b ↔ s.val ⊓ a ≤ t.val ⊓ a := by
  rw [cut_le_iff, cut_le_iff, ← wB.eq_zero_iff, ← wA.eq_zero_iff]
  have h := hab (s ⊓ tᶜ)
  simp only [map_inf, map_compl', BooleanSubalgebra.val_inf, BooleanSubalgebra.val_compl] at h
  rw [h]

theorem booleanContent_patch_le_iff (s t u v : S) :
    booleanPatch b (e s).val (e t).val ≤ booleanPatch b (e u).val (e v).val ↔
      booleanPatch a s.val t.val ≤ booleanPatch a u.val v.val := by
  rw [booleanPatch_le_iff, booleanPatch_le_iff]
  exact and_congr (matching_cut_le wA wB S T e he a b hab s u)
    (matching_cut_le wA wB S T e he aᶜ bᶜ
      (booleanContent_compl_intersection wA wB S T e he a b hab) t v)

theorem booleanContent_patch_eq (s t : S) :
    wB (booleanPatch b (e s).val (e t).val) = wA (booleanPatch a s.val t.val) := by
  rw [wB.patch, wA.patch, hab s, booleanContent_compl_intersection wA wB S T e he a b hab t]

theorem exists_booleanOrderIso_adjoin_generator :
    ∃ g : booleanAdjoinOne S a ≃o booleanAdjoinOne T b,
      (∀ s : S, (g ⟨s.val, booleanAdjoinOne_base S a s.property⟩).val = (e s).val) ∧
      (g ⟨a, booleanAdjoinOne_generator S a⟩).val = b ∧
      (∀ x, wB (g x).val = wA x.val) := by
  let pA := booleanAdjoinOnePairMap S a
  let pB := booleanAdjoinOnePairMap T b
  let E : S × S → T × T := fun st => (e st.1, e st.2)
  let r := Function.surjInv (booleanAdjoinOnePairMap_surjective S a)
  have hr (x : booleanAdjoinOne S a) : pA (r x) = x :=
    Function.rightInverse_surjInv (booleanAdjoinOnePairMap_surjective S a) x
  have hord (st uv : S × S) : pB (E st) ≤ pB (E uv) ↔ pA st ≤ pA uv :=
    booleanContent_patch_le_iff wA wB S T e he a b hab st.1 st.2 uv.1 uv.2
  let f : booleanAdjoinOne S a → booleanAdjoinOne T b := fun x => pB (E (r x))
  have hf (st : S × S) : f (pA st) = pB (E st) := by
    apply le_antisymm
    · exact (hord _ _).mpr (hr (pA st)).le
    · exact (hord _ _).mpr (hr (pA st)).ge
  have hfle (x y : booleanAdjoinOne S a) : f x ≤ f y ↔ x ≤ y := by
    change pB (E (r x)) ≤ pB (E (r y)) ↔ _
    rw [hord, hr, hr]
  have hfinj : Function.Injective f := by
    intro x y h
    exact le_antisymm ((hfle x y).mp h.le) ((hfle y x).mp h.ge)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨⟨s,t⟩,hy⟩ := booleanAdjoinOnePairMap_surjective T b y
    refine ⟨pA (e.symm s, e.symm t), ?_⟩
    rw [hf]
    simpa only [E, LinearEquiv.apply_symm_apply, OrderIso.apply_symm_apply] using hy
  let g : booleanAdjoinOne S a ≃o booleanAdjoinOne T b :=
    { toEquiv := Equiv.ofBijective f ⟨hfinj,hfsurj⟩
      map_rel_iff' := by intro x y; exact hfle x y }
  have hg (st : S × S) : g (pA st) = pB (E st) := hf st
  refine ⟨g, ?_, ?_, ?_⟩
  · intro s
    have ha : pA (s,s) = ⟨s.val, booleanAdjoinOne_base S a s.property⟩ :=
      Subtype.ext (booleanPatch_same a s.val)
    have hb : (pB (E (s,s))).val = (e s).val := booleanPatch_same b (e s).val
    rw [← ha, hg]
    exact hb
  · have ha : pA (⊤,⊥) = ⟨a, booleanAdjoinOne_generator S a⟩ := by
      apply Subtype.ext
      simp [pA, booleanAdjoinOnePairMap, booleanPatch]
    rw [← ha, hg]
    change booleanPatch b (e ⊤).val (e ⊥).val = b
    simp [booleanPatch]
  · intro x
    obtain ⟨⟨s,t⟩,hx⟩ := booleanAdjoinOnePairMap_surjective S a x
    change pA (s,t) = x at hx
    rw [← hx, hg]
    exact booleanContent_patch_eq wA wB S T e he a b hab s t

end ThesisCommon
