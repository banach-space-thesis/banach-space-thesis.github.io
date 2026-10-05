import Posets.OrdinalVariableUnitParameters

/-! Compact clopen outer blocks for a cofinal sequence of varying rank units.
Each block is the actual translated copy of the corresponding source interval. -/

noncomputable section
open Set Filter Topology
universe u
namespace Posets

namespace OrdinalVariableUnitParameters
variable {γ : Ordinal.{u}} {N : ℕ} (P : OrdinalVariableUnitParameters γ N)

theorem outer_block_shift (n : ℕ) :
    (Ordinal.omega0 ^ P.outerRank n + 1) + P.source n = P.source n := by
  apply Ordinal.principal_add_iff_add_left_eq_self.mp (Ordinal.principal_add_omega0_opow _)
  have hlt : Ordinal.omega0 ^ P.outerRank n < P.source n :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (P.sourceStrictMono (Nat.lt_succ_self n))
  have hlim : Order.IsSuccLimit (P.source n) :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (P.outerRank_pos (n+1)).ne'
  simpa only [Ordinal.add_one_eq_succ] using hlim.succ_lt hlt

def embedding (n : ℕ) : C(Iic (P.source n), Iio (Ordinal.omega0 ^ γ)) :=
  ordinalOuterBlockMap _ _ _ (P.outer_block_shift n)
    ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (P.source_lt (n+1)))

theorem embedding_isOpen (n : ℕ) : IsOpenEmbedding (P.embedding n) :=
  ordinalOuterBlockMap_isOpenEmbedding _ _ _ _ _

def outerBlock (n : ℕ) : Set (Iio (Ordinal.omega0 ^ γ)) := range (P.embedding n)

theorem outerBlock_mem_iff (n : ℕ) (x : Iio (Ordinal.omega0 ^ γ)) :
    x ∈ P.outerBlock n ↔ Ordinal.omega0 ^ P.outerRank n < x.val ∧ x.val ≤ P.source n := by
  unfold outerBlock embedding
  rw [ordinalOuterBlockMap_range]
  rfl

theorem outerBlock_isCompact (n : ℕ) : IsCompact (P.outerBlock n) :=
  ordinalOuterBlockMap_isCompact_range _ _ _ _ _

theorem outerBlock_isClopen (n : ℕ) : IsClopen (P.outerBlock n) :=
  ordinalOuterBlockMap_isClopen_range _ _ _ _ _

theorem outerBlock_disjoint : Pairwise (fun i j => Disjoint (P.outerBlock i) (P.outerBlock j)) := by
  have hlt (i j : ℕ) (hij : i < j) : Disjoint (P.outerBlock i) (P.outerBlock j) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    rw [P.outerBlock_mem_iff] at hxi hxj
    exact hxj.1.not_ge (hxi.2.trans (Ordinal.opow_le_opow_right Ordinal.omega0_pos
      (P.sourceStrictMono.monotone (Nat.succ_le_iff.mpr hij))))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

theorem outerBlock_escape (hγ : Order.IsSuccLimit γ)
    (S : Set (Iio (Ordinal.omega0 ^ γ))) (hS : IsCompact S) :
    ∀ᶠ n in cofinite, Disjoint S (P.outerBlock n) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  let B : Set Ordinal.{u} := Subtype.val '' S
  have hB : IsCompact B := hS.image continuous_subtype_val
  have hBne : B.Nonempty := hne.image _
  have hsup : sSup B < Ordinal.omega0 ^ γ := by
    obtain ⟨x, _, hx⟩ := hB.sSup_mem hBne
    exact hx ▸ x.property
  obtain ⟨β, hβ, hsβ⟩ :=
    (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hγ).mp hsup
  obtain ⟨M, hM⟩ := P.outerRank_cofinal β hβ
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop M] with n hn
  apply disjoint_left.mpr
  intro x hxS hxG
  have hxB : x.val ∈ B := ⟨x, hxS, rfl⟩
  have hxsmall : x.val < Ordinal.omega0 ^ P.outerRank n :=
    (le_csSup hB.bddAbove hxB).trans_lt (hsβ.trans_le
      (Ordinal.opow_le_opow_right Ordinal.omega0_pos (hM.le.trans (P.sourceStrictMono.monotone hn))))
  exact ((P.outerBlock_mem_iff n x).mp hxG).1.not_ge hxsmall.le

end OrdinalVariableUnitParameters
end Posets
