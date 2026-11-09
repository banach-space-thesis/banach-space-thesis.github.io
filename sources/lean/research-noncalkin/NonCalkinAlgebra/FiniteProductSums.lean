import NonCalkinAlgebra.ProductBlockRefinement
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
universe u v
variable {ι : Type u} {T : ι → Type u}

/-- Restrict a product of nonempty types to its finite set of possibly nonsingleton coordinates. -/
def restrictProduct (s : Finset ι) [∀ i, Nonempty (T i)]
    (hs : ∀ i ∉ s, Subsingleton (T i)) : (∀ i, T i) ≃ (∀ i : s, T i) := by
  classical
  refine
    { toFun := fun x i => x i
      invFun := fun x i => if hi : i ∈ s then x ⟨i, hi⟩ else Classical.choice inferInstance
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    funext i
    by_cases hi : i ∈ s
    · simp [hi]
    · letI := hs i hi
      exact Subsingleton.elim _ _
  · intro x
    funext i
    simp [i.property]

/-- Factor a weighted sum of finite coordinate products. -/
theorem sum_product_factors [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)]
    [Fintype (∀ i, T i)] {R : Type v} [CommSemiring R] (s : Finset ι)
    (hs : ∀ i ∉ s, Subsingleton (T i)) (w : ∀ i, T i → R) :
    (∑ x : ∀ i, T i, ∏ i ∈ s, w i (x i)) = ∏ i ∈ s, ∑ x : T i, w i x := by
  classical
  let e := restrictProduct (T := T) s hs
  calc
    _ = ∑ x : ∀ i, T i, ∏ i : s, w i (e x i) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Finset.prod_coe_sort s (fun i => w i (x i))).symm
    _ = ∑ x : ∀ i : s, T i, ∏ i : s, w i (x i) :=
      e.sum_comp (fun x => ∏ i : s, w i (x i))
    _ = ∏ i : s, ∑ x : T i, w i x := (Fintype.prod_sum (fun (i : s) x => w i x)).symm
    _ = _ := Finset.prod_coe_sort s (fun i => ∑ x : T i, w i x)

/-- Distribute the sigma of choices over all coordinates. -/
def productSigma {C : ι → Type u} {P : ∀ i, C i → Type u} :
    (Σ c : ∀ i, C i, ∀ i, P i (c i)) ≃ (∀ i, Σ c : C i, P i c) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end NonCalkinAlgebra.FiniteBlockRefinement
