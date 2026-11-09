import SurveyStatements.P5DyadicGridOperator
import SurveyStatements.P5Support.LpHaarDyadicRefinement

/-! Exact pointwise refinement of dyadic step values, including vectors. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace SurveyStatements.P5
open P5Support
variable {E : Type*} [AddCommMonoid E]

def dyadicGridValue (n : ℕ) (a : Fin (2 ^ n) → E) (x : ℝ) : E :=
  ∑ k : Fin (2 ^ n), (lpHaarCell n k).indicator (fun _ => a k) x

theorem dyadicGridValue_of_mem (n : ℕ) (a : Fin (2 ^ n) → E)
    (k : Fin (2 ^ n)) {x : ℝ} (hx : x ∈ lpHaarCell n k) :
    dyadicGridValue n a x = a k := by
  have hsum : (∑ j : Fin (2 ^ n), (lpHaarCell n j).indicator (fun _ => a j) x) =
      (lpHaarCell n k).indicator (fun _ => a k) x := by
    apply Finset.sum_eq_single k
    · intro j _ hjk
      have hxj : x ∉ lpHaarCell n j :=
        (lpHaarLevelCells_disjoint n hjk.symm).notMem_of_mem_left hx
      simp [hxj]
    · simp
  exact hsum.trans (Set.indicator_of_mem hx _)

theorem dyadicGridValue_of_outside (n : ℕ) (a : Fin (2 ^ n) → E)
    {x : ℝ} (hx : ∀ k : Fin (2 ^ n), x ∉ lpHaarCell n k) :
    dyadicGridValue n a x = 0 := by
  unfold dyadicGridValue
  apply Finset.sum_eq_zero
  intro k _
  simp [hx k]

theorem dyadicFineCell_subset_parent (n : ℕ) (j : Fin (2 ^ (n + 1))) :
    lpHaarCell (n + 1) j ⊆ lpHaarCell n (lpHaarParentIndex n j) := by
  rw [← lpHaarCell_children n (lpHaarParentIndex n j).val]
  change lpHaarCell (n + 1) j.val ⊆
    lpHaarCell (n + 1) (2 * (j.val / 2)) ∪ lpHaarCell (n + 1) (2 * (j.val / 2) + 1)
  intro x hx
  have hj : j.val = 2 * (j.val / 2) ∨ j.val = 2 * (j.val / 2) + 1 := by omega
  rcases hj with hj | hj
  · exact Or.inl ((congrArg (lpHaarCell (n + 1)) hj) ▸ hx)
  · exact Or.inr ((congrArg (lpHaarCell (n + 1)) hj) ▸ hx)

theorem dyadicCoarseCell_has_fine_member (n : ℕ) (k : Fin (2 ^ n))
    {x : ℝ} (hx : x ∈ lpHaarCell n k) :
    ∃ j : Fin (2 ^ (n + 1)), x ∈ lpHaarCell (n + 1) j := by
  rw [← lpHaarCell_children] at hx
  have hbound : 2 * k.val + 1 < 2 ^ (n + 1) := by
    have hk := k.isLt
    rw [pow_succ]
    omega
  rcases hx with hx | hx
  · exact ⟨⟨2 * k.val, by omega⟩, hx⟩
  · exact ⟨⟨2 * k.val + 1, hbound⟩, hx⟩

theorem dyadicGridValue_refine (n : ℕ) (a : Fin (2 ^ n) → E) (x : ℝ) :
    dyadicGridValue (n + 1) (fun j => a (lpHaarParentIndex n j)) x =
      dyadicGridValue n a x := by
  by_cases hmem : ∃ j : Fin (2 ^ (n + 1)), x ∈ lpHaarCell (n + 1) j
  · obtain ⟨j, hj⟩ := hmem
    rw [dyadicGridValue_of_mem _ _ j hj,
      dyadicGridValue_of_mem _ _ (lpHaarParentIndex n j) (dyadicFineCell_subset_parent n j hj)]
  · have hfin (j : Fin (2 ^ (n + 1))) : x ∉ lpHaarCell (n + 1) j :=
      fun hj => hmem ⟨j, hj⟩
    have hcoarse (k : Fin (2 ^ n)) : x ∉ lpHaarCell n k :=
      fun hk => hmem (dyadicCoarseCell_has_fine_member n k hk)
    rw [dyadicGridValue_of_outside _ _ hfin, dyadicGridValue_of_outside _ _ hcoarse]

end SurveyStatements.P5
