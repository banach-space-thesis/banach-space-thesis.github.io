import ThesisCommon.Analysis.DyadicTreeFrontierUpdates
import Mathlib.Analysis.SpecificLimits.Normed

/-! The finite row count and one fixed summable error budget for the
node-by-node selected-tree construction. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

def dyadicColumnErrorRows (n : ℕ) : Finset DyadicTreeNode :=
  dyadicEnumerationInitial (n+1) ∪ dyadicTreeFrontier (n+1)

theorem dyadicColumnErrorRows_card (n : ℕ) : (dyadicColumnErrorRows n).card=2*n+3 := by
  classical
  have hd : Disjoint (dyadicEnumerationInitial (n+1)) (dyadicTreeFrontier (n+1)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    exact (not_lt_of_ge ((mem_dyadicTreeFrontier (n+1) t).mp hu).1)
      ((mem_dyadicEnumerationInitial t (n+1)).mp ht)
  rw [dyadicColumnErrorRows,Finset.card_union_of_disjoint hd,card_dyadicTreeFrontier]
  simp only [dyadicEnumerationInitial,Finset.card_map,Finset.card_range]
  omega

theorem dyadicColumnErrorRows_current (n : ℕ) : dyadicTreeEnumeration n∈dyadicColumnErrorRows n := by
  apply Finset.mem_union_left
  simp only [mem_dyadicEnumerationInitial,Equiv.symm_apply_apply,Nat.lt_succ_self]

def jamesTreeColumnErrorWeight (t : DyadicTreeNode) : ℝ :=
  (1/12)*(1/2 : ℝ)^(dyadicTreeEnumeration.symm t)

def jamesTreePruningTolerance (n : ℕ) : ℝ :=
  ((1/12)*(1/2 : ℝ)^n)/(4*n+6)

theorem jamesTreePruningTolerance_pos (n : ℕ) : 0<jamesTreePruningTolerance n := by
  unfold jamesTreePruningTolerance
  positivity

theorem jamesTreeColumnErrorWeight_summable : Summable jamesTreeColumnErrorWeight := by
  have hn : Summable (fun n : ℕ => jamesTreeColumnErrorWeight (dyadicTreeEnumeration n)) := by
    simpa only [jamesTreeColumnErrorWeight,Equiv.symm_apply_apply] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ)≤1/2)
        (by norm_num : (1/2 : ℝ)<1)).mul_left (1/12)
  exact dyadicTreeEnumeration.summable_iff.mp hn

theorem jamesTreeColumnErrorWeight_tsum : (∑' t,jamesTreeColumnErrorWeight t)=1/6 := by
  rw [←dyadicTreeEnumeration.tsum_eq jamesTreeColumnErrorWeight]
  simp only [jamesTreeColumnErrorWeight,Equiv.symm_apply_apply]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0 : ℝ)≤1/2)
    (by norm_num : (1/2 : ℝ)<1)]
  norm_num

theorem jamesTreePruningTolerance_budget (n : ℕ) :
    (dyadicColumnErrorRows n).card*(2*jamesTreePruningTolerance n)=
      jamesTreeColumnErrorWeight (dyadicTreeEnumeration n) := by
  rw [dyadicColumnErrorRows_card]
  simp only [jamesTreePruningTolerance,jamesTreeColumnErrorWeight,Equiv.symm_apply_apply,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have h : (4*(n : ℝ)+6)≠0 := by positivity
  field_simp
  ring

end ThesisCommon
