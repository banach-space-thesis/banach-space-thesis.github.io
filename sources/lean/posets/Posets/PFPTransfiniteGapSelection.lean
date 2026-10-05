import Posets.TransfiniteOrdinalColorSelection
import Mathlib.SetTheory.Ordinal.Principal

/-! Actual preimages of a cofinal increasing subfamily of an arbitrary
full-cardinality injection. A successor shift supplies strict prefix gaps
for every nonzero additive-principal endpoint family. -/

noncomputable section
open Set Order
universe u
namespace Posets.PFPTransfinite

theorem ordinalInitial_injective_range_cofinal {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (k : Iio c.ord → Iio c.ord)
    (hk : Function.Injective k) (i : Iio c.ord) :
    ∃ j : Iio c.ord, i < k j := by
  classical
  by_contra hn
  push_neg at hn
  let f : Iio c.ord → Iio (succ i.val) := fun j =>
    ⟨(k j).val, (show (k j).val ≤ i.val from hn j).trans_lt (lt_succ i.val)⟩
  have hf : Function.Injective f := by
    intro j j' h
    apply hk
    apply Subtype.ext
    exact congrArg (fun x : Iio (succ i.val) => x.val) h
  have hcard := Cardinal.mk_le_of_injective hf
  rw [Ordinal.mk_Iio_ordinal, Ordinal.mk_Iio_ordinal, Cardinal.card_ord] at hcard
  have hsmall : (succ i.val).card < c := Cardinal.lt_ord.mp
    ((Cardinal.isSuccLimit_ord hc).succ_lt i.property)
  exact hsmall.not_ge (Cardinal.lift_le.mp hcard)

theorem ordinalPrincipalEndpoint_successor_selection_gap {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (e : Iio c.ord → Iio c.ord) (he : StrictMono e)
    (endpoint : Iio c.ord → Ordinal.{u}) (hθ : StrictMono endpoint)
    (hprincipal : ∀ i, Ordinal.Principal (· + ·) (endpoint i))
    (hpositive : ∀ i, endpoint i ≠ 0) (i : Iio c.ord) :
    ∃ b < endpoint (e ⟨succ i.val, (Cardinal.isSuccLimit_ord hc).succ_lt i.property⟩),
      ∀ j : Iio c.ord, j < i →
        endpoint (e ⟨succ j.val, (Cardinal.isSuccLimit_ord hc).succ_lt j.property⟩) < b := by
  let si : Iio c.ord := ⟨succ i.val, (Cardinal.isSuccLimit_ord hc).succ_lt i.property⟩
  have his : i < si := show i.val < succ i.val from lt_succ i.val
  have hθis : endpoint (e i) < endpoint (e si) := hθ (he his)
  have hlarge : 1 < endpoint (e si) :=
    (Ordinal.one_le_iff_ne_zero.mpr (hpositive (e i))).trans_lt hθis
  refine ⟨succ (endpoint (e i)),
    (Ordinal.isSuccLimit_of_principal_add hlarge (hprincipal (e si))).succ_lt hθis, ?_⟩
  intro j hji
  have hjs : (⟨succ j.val, (Cardinal.isSuccLimit_ord hc).succ_lt j.property⟩ : Iio c.ord) ≤ i :=
    show succ j.val ≤ i.val from succ_le_of_lt (show j.val < i.val from hji)
  exact (hθ.monotone (he.monotone hjs)).trans_lt (lt_succ _)

theorem exists_regularOrdinal_injective_principal_gap_selection {c : Cardinal.{u}}
    (hc : c.IsRegular) (endpoint : Iio c.ord → Ordinal.{u})
    (hθ : StrictMono endpoint)
    (hprincipal : ∀ i, Ordinal.Principal (· + ·) (endpoint i))
    (hpositive : ∀ i, endpoint i ≠ 0)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    ∃ r : Iio c.ord → Iio c.ord, Function.Injective r ∧
      StrictMono (k ∘ r) ∧ (∀ i, i < k (r i)) ∧
      (∀ β < c.ord, ∃ i, β < (k (r i)).val) ∧
      ∀ i, ∃ b < endpoint (k (r i)), ∀ j, j < i → endpoint (k (r j)) < b := by
  classical
  have hp : ∀ i : Iio c.ord, ∃ j : Iio c.ord, i < j ∧ j ∈ range k := by
    intro i
    obtain ⟨j, hj⟩ := ordinalInitial_injective_range_cofinal hc.aleph0_le k hk i
    exact ⟨k j, hj, ⟨j, rfl⟩⟩
  obtain ⟨e, he, hindex, hrange⟩ := Posets.TransfiniteOrdinal.exists_regularOrdinal_cofinal_selection hc
    (fun j => j ∈ range k) hp
  let s (i : Iio c.ord) : Iio c.ord :=
    ⟨succ i.val, (Cardinal.isSuccLimit_ord hc.aleph0_le).succ_lt i.property⟩
  have hs : StrictMono s := fun i j hij =>
    show succ i.val < succ j.val from succ_lt_succ (show i.val < j.val from hij)
  have hsi (i : Iio c.ord) : i < s i :=
    show i.val < succ i.val from lt_succ i.val
  choose r hr using fun i => hrange (s i)
  have hkr : k ∘ r = e ∘ s := funext hr
  have hstrict : StrictMono (k ∘ r) := by rw [hkr]; exact he.comp hs
  refine ⟨r, ?_, hstrict, ?_, ?_, ?_⟩
  · intro i j hij
    exact hstrict.injective (congrArg k hij)
  · intro i
    rw [hr i]
    exact (hsi i).trans_le (hindex (s i))
  · intro β hβ
    refine ⟨⟨β, hβ⟩, ?_⟩
    rw [hr]
    exact (hsi ⟨β, hβ⟩).trans_le (hindex (s ⟨β, hβ⟩))
  · intro i
    simp only [hr]
    exact ordinalPrincipalEndpoint_successor_selection_gap hc.aleph0_le e he
      endpoint hθ hprincipal hpositive i

end Posets.PFPTransfinite


