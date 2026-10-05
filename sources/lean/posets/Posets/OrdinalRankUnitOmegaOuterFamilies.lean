import Posets.OrdinalRankUnitOmegaOuterBlocks

/-! Disjointness and escape of the actual outer blocks. Any strictly
increasing sequence of finite heights supplies compact clopen blocks
eventually disjoint from every compact subset of the half-open space. -/

noncomputable section
open Set Filter Topology
universe u
namespace Posets

def ordinalRankUnitOmegaOuterFamily (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ)
    (h : ℕ → ℕ) (hh : StrictMono h) (n : ℕ) :
    Set (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) :=
  range (ordinalRankUnitOmegaOuterBlock ρ hρ (h n) (h (n+1)) (hh (Nat.lt_succ_self n)))

theorem ordinalRankUnitOmegaOuterFamily_mem_iff
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) (h : ℕ → ℕ) (hh : StrictMono h)
    (n : ℕ) (x : Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) :
    x ∈ ordinalRankUnitOmegaOuterFamily ρ hρ h hh n ↔
      ordinalRankUnitOmegaBase ρ ^ (h n : Ordinal) < x.val ∧ x.val ≤ ordinalRankUnitOmegaBase ρ ^ (h (n+1) : Ordinal) := by
  rw [ordinalRankUnitOmegaOuterFamily, ordinalRankUnitOmegaOuterBlock, ordinalOuterBlockMap_range]
  rfl

theorem ordinalRankUnitOmegaOuterFamily_isCompact
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) (h : ℕ → ℕ) (hh : StrictMono h) (n : ℕ) :
    IsCompact (ordinalRankUnitOmegaOuterFamily ρ hρ h hh n) :=
  ordinalOuterBlockMap_isCompact_range _ _ _ _ _

theorem ordinalRankUnitOmegaOuterFamily_isClopen
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) (h : ℕ → ℕ) (hh : StrictMono h) (n : ℕ) :
    IsClopen (ordinalRankUnitOmegaOuterFamily ρ hρ h hh n) :=
  ordinalOuterBlockMap_isClopen_range _ _ _ _ _

theorem ordinalRankUnitOmegaOuterFamily_disjoint
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) (h : ℕ → ℕ) (hh : StrictMono h) :
    Pairwise (fun i j => Disjoint (ordinalRankUnitOmegaOuterFamily ρ hρ h hh i)
      (ordinalRankUnitOmegaOuterFamily ρ hρ h hh j)) := by
  have hκ : 0 < ordinalRankUnitOmegaBase ρ := ordinalRankUnitOmegaBase_pos ρ
  have hlt (i j : ℕ) (hij : i < j) :
      Disjoint (ordinalRankUnitOmegaOuterFamily ρ hρ h hh i)
        (ordinalRankUnitOmegaOuterFamily ρ hρ h hh j) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    rw [ordinalRankUnitOmegaOuterFamily_mem_iff] at hxi hxj
    exact hxj.1.not_ge (hxi.2.trans (Ordinal.opow_le_opow_right hκ
      (by exact_mod_cast hh.monotone (Nat.succ_le_iff.mpr hij))))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

theorem ordinalRankUnitOmegaOuterFamily_escape
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) (h : ℕ → ℕ) (hh : StrictMono h)
    (S : Set (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))) (hS : IsCompact S) :
    ∀ᶠ n in cofinite, Disjoint S (ordinalRankUnitOmegaOuterFamily ρ hρ h hh n) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hκ : 0 < ordinalRankUnitOmegaBase ρ := ordinalRankUnitOmegaBase_pos ρ
  let B : Set Ordinal.{u} := Subtype.val '' S
  have hB : IsCompact B := hS.image continuous_subtype_val
  have hBne : B.Nonempty := hne.image _
  have hsup : sSup B < ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0 := by
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
  have hxsmall : x.val < ordinalRankUnitOmegaBase ρ ^ (h n : Ordinal) :=
    (le_csSup hB.bddAbove hxB).trans_lt (hsβ.trans_le
      (Ordinal.opow_le_opow_right hκ (by exact_mod_cast hn.trans (hh.id_le n))))
  exact ((ordinalRankUnitOmegaOuterFamily_mem_iff ρ hρ h hh n x).mp hxG).1.not_ge hxsmall.le

end Posets

