import Posets.OrdinalRegularOmegaOuterBlocks

/-! Disjointness and escape of the actual outer blocks. Any strictly
increasing sequence of finite heights supplies compact clopen blocks
eventually disjoint from every compact subset of the half-open space. -/

noncomputable section
open Set Filter Topology
universe u
namespace Posets

def ordinalRegularOmegaOuterFamily (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (n : ℕ) :
    Set (Iio (c.ord ^ Ordinal.omega0)) :=
  range (ordinalRegularOmegaOuterBlock c hc (h n) (h (n+1)) (hh (Nat.lt_succ_self n)))

theorem ordinalRegularOmegaOuterFamily_mem_iff
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h)
    (n : ℕ) (x : Iio (c.ord ^ Ordinal.omega0)) :
    x ∈ ordinalRegularOmegaOuterFamily c hc h hh n ↔
      c.ord ^ (h n : Ordinal) < x.val ∧ x.val ≤ c.ord ^ (h (n+1) : Ordinal) := by
  rw [ordinalRegularOmegaOuterFamily, ordinalRegularOmegaOuterBlock, ordinalOuterBlockMap_range]
  rfl

theorem ordinalRegularOmegaOuterFamily_isCompact
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (n : ℕ) :
    IsCompact (ordinalRegularOmegaOuterFamily c hc h hh n) :=
  ordinalOuterBlockMap_isCompact_range _ _ _ _ _

theorem ordinalRegularOmegaOuterFamily_isClopen
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (n : ℕ) :
    IsClopen (ordinalRegularOmegaOuterFamily c hc h hh n) :=
  ordinalOuterBlockMap_isClopen_range _ _ _ _ _

theorem ordinalRegularOmegaOuterFamily_disjoint
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) :
    Pairwise (fun i j => Disjoint (ordinalRegularOmegaOuterFamily c hc h hh i)
      (ordinalRegularOmegaOuterFamily c hc h hh j)) := by
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc)
  have hlt (i j : ℕ) (hij : i < j) :
      Disjoint (ordinalRegularOmegaOuterFamily c hc h hh i)
        (ordinalRegularOmegaOuterFamily c hc h hh j) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    rw [ordinalRegularOmegaOuterFamily_mem_iff] at hxi hxj
    exact hxj.1.not_ge (hxi.2.trans (Ordinal.opow_le_opow_right hκ
      (by exact_mod_cast hh.monotone (Nat.succ_le_iff.mpr hij))))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

theorem ordinalRegularOmegaOuterFamily_escape
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h)
    (S : Set (Iio (c.ord ^ Ordinal.omega0))) (hS : IsCompact S) :
    ∀ᶠ n in cofinite, Disjoint S (ordinalRegularOmegaOuterFamily c hc h hh n) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc)
  let B : Set Ordinal.{u} := Subtype.val '' S
  have hB : IsCompact B := hS.image continuous_subtype_val
  have hBne : B.Nonempty := hne.image _
  have hsup : sSup B < c.ord ^ Ordinal.omega0 := by
    obtain ⟨x, _, hx⟩ := hB.sSup_mem hBne
    exact hx ▸ x.property
  obtain ⟨β, hβ, hsβ⟩ :=
    (Ordinal.lt_opow_of_isSuccLimit hκ.ne' Ordinal.isSuccLimit_omega0).mp hsup
  obtain ⟨N, rfl⟩ := Ordinal.lt_omega0.mp hβ
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop N] with n hn
  apply disjoint_left.mpr
  intro x hxS hxG
  have hxB : x.val ∈ B := ⟨x, hxS, rfl⟩
  have hxsmall : x.val < c.ord ^ (h n : Ordinal) :=
    (le_csSup hB.bddAbove hxB).trans_lt (hsβ.trans_le
      (Ordinal.opow_le_opow_right hκ (by exact_mod_cast hn.trans (hh.id_le n))))
  exact ((ordinalRegularOmegaOuterFamily_mem_iff c hc h hh n x).mp hxG).1.not_ge hxsmall.le

end Posets
