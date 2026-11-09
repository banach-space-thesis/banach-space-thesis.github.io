import ThesisCommon.Analysis.LpHaarPartitionTree
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact finite-sum decomposition into the two dyadic children. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

def lpHaarChildrenEquiv (n : ℕ) : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ 2 n).symm)

theorem lpHaarChildrenEquiv_left (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarChildrenEquiv n (k, 0) = lpHaarLeftIndex n k := by
  apply Fin.ext
  change 0 + 2 * k.val = 2 * k.val + 0
  omega

theorem lpHaarChildrenEquiv_right (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarChildrenEquiv n (k, 1) = lpHaarRightIndex n k := by
  apply Fin.ext
  change 1 + 2 * k.val = 2 * k.val + 1
  omega

theorem lpHaar_child_indices_ne (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarLeftIndex n k ≠ lpHaarRightIndex n k := by
  intro h
  have hv := congrArg Fin.val h
  change 2 * k.val + 0 = 2 * k.val + 1 at hv
  omega

theorem lpHaar_sum_children {E : Type*} [AddCommMonoid E] (n : ℕ)
    (f : Fin (2 ^ (n + 1)) → E) :
    (∑ j, f j) = ∑ k : Fin (2 ^ n),
      (f (lpHaarLeftIndex n k) + f (lpHaarRightIndex n k)) := by
  rw [← (lpHaarChildrenEquiv n).sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin.sum_univ_two, lpHaarChildrenEquiv_left, lpHaarChildrenEquiv_right]

end ThesisCommon
