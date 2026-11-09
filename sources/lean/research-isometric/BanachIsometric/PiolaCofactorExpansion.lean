import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic

/-!
# Row-permutation cofactor expansion for the Piola cancellation

The matrix convention is row = output coordinate, column = input direction.
The expansion follows from the actual adjugate and a determinant with one
row replaced by a coordinate vector. Transposition puts the Leibniz formula
in the row-permutation convention used in the Hessian cancellation.
-/

namespace BanachIsometric

open scoped BigOperators

theorem adjugate_apply_eq_sum_permutations_erase
    {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℝ) (i j : κ) :
    A.adjugate i j = ∑ σ : Equiv.Perm κ,
      if σ j = i then ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ k ∈ Finset.univ.erase j, A k (σ k) else 0 := by
  rw [Matrix.adjugate_apply, ← Matrix.det_transpose (A.updateRow j (Pi.single i 1)),
    Matrix.det_apply']
  simp only [Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k ↦ A.updateRow j (Pi.single i 1) k (σ k)) (Finset.mem_univ j)]
  have hrest : (∏ k ∈ Finset.univ.erase j, A.updateRow j (Pi.single i 1) k (σ k)) =
      ∏ k ∈ Finset.univ.erase j, A k (σ k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Matrix.updateRow_ne (Finset.mem_erase.mp hk).1]
  rw [Matrix.updateRow_self, hrest]
  by_cases h : σ j = i
  · simp [Pi.single_apply, h]
  · simp [h]

end BanachIsometric
