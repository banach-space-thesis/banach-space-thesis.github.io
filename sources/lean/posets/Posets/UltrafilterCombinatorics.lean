import Posets.AutomaticContinuity
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Filter.Bases.Basic

/-! Finite partition estimates for the synchronized ultrafilters of Lemma 8.1. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter
namespace Posets

/-- All selectors on a row have the same membership in each of finitely many sets. -/
def synchronizedRows (K : ℕ) (F : Finset (Set ColumnDomain)) : Set RowDomain :=
  {x | K ≤ x.1 ∧ ∀ A ∈ F, ∀ n m, selector n x ∈ A ↔ selector m x ∈ A}

/-- A block large enough for a finite Boolean partition has a monochromatic row. -/
theorem synchronizedRows_nonempty (K : ℕ) (F : Finset (Set ColumnDomain)) :
    (synchronizedRows K F).Nonempty := by
  let k := max K F.card
  let color : Block k → (F → Bool) := fun b A => decide ((⟨k, b⟩ : ColumnDomain) ∈ A.val)
  have hc : Fintype.card (F → Bool) * (k + 1) ≤ Fintype.card (Block k) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Fintype.card_fin]
    rw [Nat.mul_comm (k + 1)]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega))
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card color hc
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin (k + 1)) (s := Finset.univ.filter (fun b => color b = c)) (by simpa using hc)
  refine ⟨⟨k, e⟩, le_max_left _ _, ?_⟩
  intro A hA n m
  have hec (i : Fin (k + 1)) : color (e i) = c := by
    exact (Finset.mem_filter.mp (he ⟨i, rfl⟩)).2
  have heA (i j : Fin (k + 1)) :
      ((⟨k, e i⟩ : ColumnDomain) ∈ A ↔ (⟨k, e j⟩ : ColumnDomain) ∈ A) := by
    have hh := congrFun ((hec i).trans (hec j).symm) (⟨A, hA⟩ : F)
    simpa only [color, decide_eq_decide] using hh
  exact heA _ _

@[simp] theorem selector_block (n : ℕ) (x : RowDomain) : (selector n x).1 = x.1 := rfl

theorem selector_distinct_of_le {n m : ℕ} (hnm : n ≠ m) (x : RowDomain)
    (hn : n ≤ x.1) (hm : m ≤ x.1) : selector n x ≠ selector m x := by
  rcases x with ⟨k, e⟩
  simp only [selector, Nat.lt_succ_iff, hn, hm, dite_true]
  intro h
  have he := e.injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  exact hnm (congrArg Fin.val he)

/-- Each selector has finite fibres because it preserves the finite block. -/
theorem selector_finite_fiber (n : ℕ) (y : ColumnDomain) :
    (selector n ⁻¹' {y}).Finite := by
  refine (Set.finite_range (@Sigma.mk ℕ (fun k => Fin (k + 1) ↪ Block k) y.1)).subset ?_
  intro x hx
  have hk : x.1 = y.1 := congrArg Sigma.fst hx
  rcases x with ⟨k, e⟩
  dsimp only at hk
  subst k
  exact ⟨e, rfl⟩

theorem selector_tendsto_cofinite (n : ℕ) :
    Tendsto (selector n) cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton (selector_finite_fiber n)

end Posets
