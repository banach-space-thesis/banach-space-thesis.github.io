import ThesisCommon.Analysis.UnitCharge
import Mathlib.Analysis.Complex.Basic

/-! Complex finitely additive power-set charges with total variation at most
one. This is the complex scalar counterpart of UnitCharge, used by the modified
Sigma construction. No countable additivity or representation is assumed. -/
noncomputable section
open Set
namespace ThesisCommon

structure ComplexUnitCharge (α : Type*) where
  toFun : Set α → ℂ
  map_empty : toFun ∅ = 0
  map_union : ∀ A B, Disjoint A B → toFun (A ∪ B) = toFun A + toFun B
  variation_le : ∀ (F : Finset ℕ) (A : ℕ → Set α),
    (↑F : Set ℕ).Pairwise (fun i j => Disjoint (A i) (A j)) →
      ∑ i ∈ F, ‖toFun (A i)‖ ≤ 1

instance {α : Type*} : CoeFun (ComplexUnitCharge α) (fun _ => Set α → ℂ) :=
  ⟨ComplexUnitCharge.toFun⟩

theorem ComplexUnitCharge.ext {α : Type*} {μ ν : ComplexUnitCharge α}
    (h : μ.toFun = ν.toFun) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem ComplexUnitCharge.norm_apply_le_one {α : Type*} (μ : ComplexUnitCharge α) (A : Set α) :
    ‖μ A‖ ≤ 1 := by
  have h := μ.variation_le {0} (fun _ => A) (by simp)
  simpa using h

def ComplexUnitCharge.realPart {α : Type*} (μ : ComplexUnitCharge α) : UnitCharge α where
  toFun A := (μ A).re
  map_empty := by rw [μ.map_empty,Complex.zero_re]
  map_union A B h := by rw [μ.map_union A B h,Complex.add_re]
  variation_le F A h := (Finset.sum_le_sum (fun i _ => Complex.abs_re_le_norm (μ (A i)))).trans
    (μ.variation_le F A h)

def ComplexUnitCharge.imagPart {α : Type*} (μ : ComplexUnitCharge α) : UnitCharge α where
  toFun A := (μ A).im
  map_empty := by rw [μ.map_empty,Complex.zero_im]
  map_union A B h := by rw [μ.map_union A B h,Complex.add_im]
  variation_le F A h := (Finset.sum_le_sum (fun i _ => Complex.abs_im_le_norm (μ (A i)))).trans
    (μ.variation_le F A h)

def UnitCharge.toComplex {α : Type*} (μ : UnitCharge α) : ComplexUnitCharge α where
  toFun A := (μ A : ℂ)
  map_empty := by rw [μ.map_empty,Complex.ofReal_zero]
  map_union A B h := by rw [μ.map_union A B h,Complex.ofReal_add]
  variation_le F A h := by simpa using μ.variation_le F A h

theorem ComplexUnitCharge.diff_add_inter {α : Type*} (μ : ComplexUnitCharge α) (A Z : Set α) :
    μ (A \ Z) + μ (A ∩ Z) = μ A := by
  rw [← μ.map_union _ _ (by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 hy.2)]
  congr 1
  ext x
  simp only [Set.mem_union,Set.mem_diff,Set.mem_inter_iff]
  tauto

theorem ComplexUnitCharge.split_test {α : Type*} (μ : ComplexUnitCharge α) (A B Z : Set α) :
    μ ((A ∩ Z) ∪ (B \ Z)) = μ B + μ (A ∩ Z) - μ (B ∩ Z) := by
  rw [μ.map_union _ _ (by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 hx.2),← μ.diff_add_inter B Z]
  ring

def ComplexUnitCharge.comapEmbedding {α β : Type*} (μ : ComplexUnitCharge β) (e : α ↪ β) :
    ComplexUnitCharge α where
  toFun A := μ (e '' A)
  map_empty := by simpa using μ.map_empty
  map_union A B h := by
    rw [Set.image_union]
    exact μ.map_union _ _ (Set.disjoint_image_of_injective e.injective h)
  variation_le F A h := μ.variation_le F (fun i => e '' A i) (fun i hi j hj hne =>
    Set.disjoint_image_of_injective e.injective (h hi hj hne))

theorem ComplexUnitCharge.variation_fin {α : Type*} (μ : ComplexUnitCharge α) {n : ℕ}
    (A : Fin n → Set α) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ i, ‖μ (A i)‖ ≤ 1 := by
  classical
  let B : ℕ → Set α := fun i => if hi : i < n then A ⟨i,hi⟩ else ∅
  have hB : (↑(Finset.range n) : Set ℕ).Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i hi j hj hne
    have hi' : i < n := Finset.mem_range.mp hi
    have hj' : j < n := Finset.mem_range.mp hj
    simpa [B,hi',hj'] using hA (i := ⟨i,hi'⟩) (j := ⟨j,hj'⟩)
      (fun h => hne (congrArg Fin.val h))
  have hh := μ.variation_le (Finset.range n) B hB
  rw [Finset.sum_range] at hh
  simpa [B] using hh

theorem ComplexUnitCharge.sum_norm_diff_le_two {α : Type*} (μ ν : ComplexUnitCharge α) {n : ℕ}
    (A : Fin n → Set α) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ i, ‖μ (A i) - ν (A i)‖ ≤ 2 := by
  calc
    _ ≤ ∑ i, (‖μ (A i)‖ + ‖ν (A i)‖) := Finset.sum_le_sum (fun i _ => norm_sub_le _ _)
    _ = (∑ i, ‖μ (A i)‖) + ∑ i, ‖ν (A i)‖ := Finset.sum_add_distrib
    _ ≤ 2 := by linarith [μ.variation_fin A hA,ν.variation_fin A hA]

end ThesisCommon
