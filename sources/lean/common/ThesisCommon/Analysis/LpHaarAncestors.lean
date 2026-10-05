import ThesisCommon.Analysis.LpHaarSubtreeProjections
import ThesisCommon.Analysis.LpHaarDyadicRefinement
import ThesisCommon.Analysis.LpHaarEnumeration

/-! Finite ancestor paths in the actual dyadic tree. Localised high-pass
operators act precisely on descendant Haar vectors. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical BigOperators
namespace ThesisCommon

theorem lpHaarCell_subset_parent (n : ℕ) (k : Fin (2 ^ (n + 1))) :
    lpHaarCell (n + 1) k ⊆ lpHaarCell n (lpHaarParentIndex n k) := by
  intro x hx
  rw [← lpHaarCell_children]
  have hdivision : k.val = 2 * (k.val / 2) ∨ k.val = 2 * (k.val / 2) + 1 := by omega
  rcases hdivision with he | he
  · apply Or.inl
    change x ∈ lpHaarCell (n + 1) (2 * (k.val / 2))
    rw [← he]
    exact hx
  · apply Or.inr
    change x ∈ lpHaarCell (n + 1) (2 * (k.val / 2) + 1)
    rw [← he]
    exact hx

def lpHaarAncestors : (n : ℕ) → Fin (2 ^ n) → Finset LpHaarTreeIndex
  | 0, k => {⟨0, k⟩}
  | n + 1, k => insert ⟨n + 1, k⟩ (lpHaarAncestors n (lpHaarParentIndex n k))

theorem lpHaarAncestors_level_le (n : ℕ) (k : Fin (2 ^ n))
    (i : LpHaarTreeIndex) (hi : i ∈ lpHaarAncestors n k) : i.1 ≤ n := by
  induction n with
  | zero =>
      have he : i = ⟨0, k⟩ := Finset.mem_singleton.mp hi
      subst i
      exact le_rfl
  | succ n ih =>
      rcases Finset.mem_insert.mp hi with he | hi
      · subst i; exact le_rfl
      · exact (ih (lpHaarParentIndex n k) hi).trans (Nat.le_succ n)

theorem lpHaarAncestors_contains (n : ℕ) (k : Fin (2 ^ n))
    (i : LpHaarTreeIndex) (hi : i ∈ lpHaarAncestors n k) :
    lpHaarCell n k ⊆ lpHaarCell i.1 i.2 := by
  induction n with
  | zero =>
      have he : i = ⟨0, k⟩ := Finset.mem_singleton.mp hi
      subst i
      exact Subset.rfl
  | succ n ih =>
      rcases Finset.mem_insert.mp hi with he | hi
      · subst i; exact Subset.rfl
      · exact (lpHaarCell_subset_parent n k).trans (ih (lpHaarParentIndex n k) hi)

theorem lpHaarAncestors_disjoint (n : ℕ) (k : Fin (2 ^ n))
    (i : LpHaarTreeIndex) (hilevel : i.1 ≤ n) (hi : i ∉ lpHaarAncestors n k) :
    Disjoint (lpHaarCell i.1 i.2) (lpHaarCell n k) := by
  induction n with
  | zero =>
      rcases i with ⟨r, j⟩
      change r ≤ 0 at hilevel
      have hr : r = 0 := by omega
      subst r
      have hj : j = k := by
        apply Fin.ext
        have hj := j.isLt
        have hk := k.isLt
        simp only [pow_zero] at hj hk
        omega
      subst j
      exact (hi (Finset.mem_singleton_self _)).elim
  | succ n ih =>
      rcases i with ⟨r, j⟩
      change r ≤ n + 1 at hilevel
      by_cases hr : r = n + 1
      · subst r
        apply lpHaarCell_disjoint_sameLevel
        intro hjk
        have hj : j = k := Fin.ext hjk
        subst j
        exact hi (Finset.mem_insert_self _ _)
      · have hparent : (⟨r, j⟩ : LpHaarTreeIndex) ∉
            lpHaarAncestors n (lpHaarParentIndex n k) :=
          fun h => hi (Finset.mem_insert_of_mem h)
        have hd := ih (lpHaarParentIndex n k) (by change r ≤ n; omega) hparent
        exact Set.disjoint_left.mpr (fun x hxi hxk =>
          Set.disjoint_left.mp hd hxi (lpHaarCell_subset_parent n k hxk))

variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem lpHaarSubtreeProjection_haar (i : LpHaarTreeIndex) (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarSubtreeProjection 𝕜 p hp i.1 i.2 (lpHaarDyadic 𝕜 p n k) =
      if i ∈ lpHaarAncestors n k then lpHaarDyadic 𝕜 p n k else 0 := by
  by_cases hi : i ∈ lpHaarAncestors n k
  · rw [if_pos hi]
    exact lpHaarSubtreeProjection_fix_contained 𝕜 p hp i.1 i.2 n k k.isLt
      (lpHaarAncestors_level_le n k i hi) (lpHaarAncestors_contains n k i hi)
  · rw [if_neg hi]
    by_cases hilevel : i.1 ≤ n
    · exact lpHaarSubtreeProjection_kill_disjoint 𝕜 p hp i.1 i.2 n k k.isLt hilevel
        (lpHaarAncestors_disjoint n k i hilevel hi)
    · exact lpHaarSubtreeProjection_kill_earlier 𝕜 p hp i.1 i.2 n k k.isLt (by omega)

end ThesisCommon
