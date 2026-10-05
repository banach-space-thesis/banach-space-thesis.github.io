import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Real finitely additive measures on a power set with total variation at most one.
The finite-variation condition uses finite indexed disjoint families and does
not impose countable additivity. -/
noncomputable section
open Set
namespace ThesisCommon

structure UnitCharge (α : Type*) where
  toFun : Set α → ℝ
  map_empty : toFun ∅ = 0
  map_union : ∀ A B, Disjoint A B → toFun (A ∪ B) = toFun A + toFun B
  variation_le : ∀ (F : Finset ℕ) (A : ℕ → Set α),
    (↑F : Set ℕ).Pairwise (fun i j => Disjoint (A i) (A j)) →
      ∑ i ∈ F, |toFun (A i)| ≤ 1

instance {α : Type*} : CoeFun (UnitCharge α) (fun _ => Set α → ℝ) := ⟨UnitCharge.toFun⟩

theorem UnitCharge.ext {α : Type*} {μ ν : UnitCharge α} (h : μ.toFun = ν.toFun) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem UnitCharge.abs_apply_le_one {α : Type*} (μ : UnitCharge α) (A : Set α) :
    |μ A| ≤ 1 := by
  have h := μ.variation_le {0} (fun _ => A) (by simp)
  simpa using h

theorem UnitCharge.diff_add_inter {α : Type*} (μ : UnitCharge α) (A Z : Set α) :
    μ (A \ Z) + μ (A ∩ Z) = μ A := by
  rw [← μ.map_union _ _ (by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 hy.2)]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
  tauto

theorem UnitCharge.split_test {α : Type*} (μ : UnitCharge α) (A B Z : Set α) :
    μ ((A ∩ Z) ∪ (B \ Z)) = μ B + μ (A ∩ Z) - μ (B ∩ Z) := by
  rw [μ.map_union _ _ (by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 hx.2)]
  linarith [μ.diff_add_inter B Z]

def UnitCharge.comapEmbedding {α β : Type*} (μ : UnitCharge β) (e : α ↪ β) : UnitCharge α where
  toFun A := μ (e '' A)
  map_empty := by simpa using μ.map_empty
  map_union A B h := by
    rw [Set.image_union]
    exact μ.map_union _ _ (Set.disjoint_image_of_injective e.injective h)
  variation_le F A h := μ.variation_le F (fun i => e '' A i) (fun i hi j hj hne =>
    Set.disjoint_image_of_injective e.injective (h hi hj hne))

theorem UnitCharge.variation_fin {α : Type*} (μ : UnitCharge α) {n : ℕ}
    (A : Fin n → Set α) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ i, |μ (A i)| ≤ 1 := by
  classical
  let B : ℕ → Set α := fun i => if hi : i < n then A ⟨i, hi⟩ else ∅
  have hB : (↑(Finset.range n) : Set ℕ).Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i hi j hj hne
    have hi' : i < n := Finset.mem_range.mp hi
    have hj' : j < n := Finset.mem_range.mp hj
    simpa [B, hi', hj'] using hA (i := ⟨i, hi'⟩) (j := ⟨j, hj'⟩)
      (fun h => hne (congrArg Fin.val h))
  have hh := μ.variation_le (Finset.range n) B hB
  rw [Finset.sum_range] at hh
  simpa [B] using hh

theorem UnitCharge.sum_abs_diff_inter_le_two {α : Type*} (μ ν : UnitCharge α) {n : ℕ}
    (Z : Fin n → Set α) (hZ : Pairwise (fun i j => Disjoint (Z i) (Z j))) (A : Set α) :
    ∑ i, |μ (A ∩ Z i) - ν (A ∩ Z i)| ≤ 2 := by
  have hd : Pairwise (fun i j => Disjoint (A ∩ Z i) (A ∩ Z j)) :=
    fun i j hij => (hZ hij).mono Set.inter_subset_right Set.inter_subset_right
  calc
    _ ≤ ∑ i, (|μ (A ∩ Z i)| + |ν (A ∩ Z i)|) :=
      Finset.sum_le_sum (fun i _ => abs_sub _ _)
    _ = (∑ i, |μ (A ∩ Z i)|) + ∑ i, |ν (A ∩ Z i)| := Finset.sum_add_distrib
    _ ≤ 2 := by linarith [μ.variation_fin (fun i => A ∩ Z i) hd,
      ν.variation_fin (fun i => A ∩ Z i) hd]

end ThesisCommon
