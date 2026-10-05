import ThesisCommon.Analysis.LpHaarSequentialSplits
import ThesisCommon.Analysis.LpHaarFaithfulRetractions

/-! The ordered binary block recursion yields a genuine measurable
partition tree. Equal atom measures, covering, disjointness and faithful
splits are proved from the finite signed children at each node. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon

def lpHaarHeapIndex (n : ℕ) (k : Fin (2 ^ n)) : ℕ := 2 ^ n + k.val - 1

theorem lpHaarHeapIndex_zero (k : Fin (2 ^ 0)) : lpHaarHeapIndex 0 k = 0 := by
  have hk := k.isLt
  simp only [pow_zero] at hk
  simp only [lpHaarHeapIndex, pow_zero]
  omega

theorem lpHaarHeapIndex_left (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarHeapIndex (n + 1) (lpHaarLeftIndex n k) = 2 * lpHaarHeapIndex n k + 1 := by
  change 2 ^ (n + 1) + (2 * k.val + 0) - 1 = 2 * (2 ^ n + k.val - 1) + 1
  rw [pow_succ]
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  omega

theorem lpHaarHeapIndex_right (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarHeapIndex (n + 1) (lpHaarRightIndex n k) = 2 * lpHaarHeapIndex n k + 2 := by
  change 2 ^ (n + 1) + (2 * k.val + 1) - 1 = 2 * (2 ^ n + k.val - 1) + 2
  rw [pow_succ]
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  omega

theorem lpHaarHeapIndex_depth_le (n : ℕ) (k : Fin (2 ^ n)) : n ≤ lpHaarHeapIndex n k := by
  have h := n.lt_two_pow_self
  unfold lpHaarHeapIndex
  omega

theorem lpHaar_split_partition_union {α : Type*} (n : ℕ)
    (s : Fin (2 ^ n) → Set α) (t : Fin (2 ^ (n + 1)) → Set α)
    (hsplit : ∀ k, t (lpHaarLeftIndex n k) ∪ t (lpHaarRightIndex n k) = s k) :
    (⋃ j, t j) = ⋃ k, s k := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hx⟩
    obtain ⟨⟨k, b⟩, rfl⟩ := (lpHaarChildrenEquiv n).surjective j
    refine ⟨k, ?_⟩
    rw [← hsplit k]
    fin_cases b
    · change x ∈ t (lpHaarChildrenEquiv n (k, 0)) at hx
      exact Or.inl (by simpa only [lpHaarChildrenEquiv_left] using hx)
    · change x ∈ t (lpHaarChildrenEquiv n (k, 1)) at hx
      exact Or.inr (by simpa only [lpHaarChildrenEquiv_right] using hx)
  · rintro ⟨k, hx⟩
    rw [← hsplit k] at hx
    rcases hx with hx | hx
    · exact ⟨lpHaarLeftIndex n k, hx⟩
    · exact ⟨lpHaarRightIndex n k, hx⟩

theorem lpHaar_split_partition_disjoint {α : Type*} (n : ℕ)
    (s : Fin (2 ^ n) → Set α) (t : Fin (2 ^ (n + 1)) → Set α)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hsplit : ∀ k, t (lpHaarLeftIndex n k) ∪ t (lpHaarRightIndex n k) = s k)
    (hchild : ∀ k, Disjoint (t (lpHaarLeftIndex n k)) (t (lpHaarRightIndex n k))) :
    Pairwise (fun i j => Disjoint (t i) (t j)) := by
  have hsub (k : Fin (2 ^ n)) (b : Fin 2) : t (lpHaarChildrenEquiv n (k, b)) ⊆ s k := by
    rw [← hsplit k]
    fin_cases b
    · change t (lpHaarChildrenEquiv n (k, 0)) ⊆ _
      rw [lpHaarChildrenEquiv_left]; exact subset_union_left
    · change t (lpHaarChildrenEquiv n (k, 1)) ⊆ _
      rw [lpHaarChildrenEquiv_right]; exact subset_union_right
  intro i j hij
  obtain ⟨⟨k, b⟩, rfl⟩ := (lpHaarChildrenEquiv n).surjective i
  obtain ⟨⟨l, c⟩, rfl⟩ := (lpHaarChildrenEquiv n).surjective j
  by_cases hkl : k = l
  · subst l
    fin_cases b <;> fin_cases c
    · exact (hij rfl).elim
    · change Disjoint (t (lpHaarChildrenEquiv n (k, 0))) (t (lpHaarChildrenEquiv n (k, 1)))
      simpa only [lpHaarChildrenEquiv_left, lpHaarChildrenEquiv_right] using hchild k
    · change Disjoint (t (lpHaarChildrenEquiv n (k, 1))) (t (lpHaarChildrenEquiv n (k, 0)))
      simpa only [lpHaarChildrenEquiv_left, lpHaarChildrenEquiv_right] using (hchild k).symm
    · exact (hij rfl).elim
  · exact (hd hkl).mono (hsub k b) (hsub l c)

namespace LpHaarSequentialSplits
variable (F : LpHaarSequentialSplits)

def cell (n : ℕ) (k : Fin (2 ^ n)) : Set ℝ := (F.node (lpHaarHeapIndex n k)).parent.set

theorem cell_left (n : ℕ) (k : Fin (2 ^ n)) :
    F.cell (n + 1) (lpHaarLeftIndex n k) = ((F.node (lpHaarHeapIndex n k)).child true).set := by
  rw [cell, lpHaarHeapIndex_left, F.left_parent]

theorem cell_right (n : ℕ) (k : Fin (2 ^ n)) :
    F.cell (n + 1) (lpHaarRightIndex n k) = ((F.node (lpHaarHeapIndex n k)).child false).set := by
  rw [cell, lpHaarHeapIndex_right, F.right_parent]

theorem cell_split (n : ℕ) (k : Fin (2 ^ n)) :
    F.cell (n + 1) (lpHaarLeftIndex n k) ∪ F.cell (n + 1) (lpHaarRightIndex n k) = F.cell n k := by
  rw [F.cell_left, F.cell_right]
  exact (F.node (lpHaarHeapIndex n k)).children_union

theorem cell_children_disjoint (n : ℕ) (k : Fin (2 ^ n)) :
    Disjoint (F.cell (n + 1) (lpHaarLeftIndex n k)) (F.cell (n + 1) (lpHaarRightIndex n k)) := by
  rw [F.cell_left, F.cell_right]
  exact (F.node (lpHaarHeapIndex n k)).children_disjoint

theorem cell_disjoint (n : ℕ) : Pairwise (fun i j => Disjoint (F.cell n i) (F.cell n j)) := by
  induction n with
  | zero =>
      intro i j hij
      have hi := i.isLt
      have hj := j.isLt
      simp only [pow_zero] at hi hj
      exact (hij (Fin.ext (by omega))).elim
  | succ n ih =>
      exact lpHaar_split_partition_disjoint n (F.cell n) (F.cell (n + 1)) ih
        (F.cell_split n) (F.cell_children_disjoint n)

theorem cell_union (n : ℕ) : (⋃ k, F.cell n k) = lpHaarCell 0 0 := by
  induction n with
  | zero =>
      simp only [cell, lpHaarHeapIndex_zero, F.root_set, LpHaarFiniteParent.root_set,
        iUnion_const]
  | succ n ih => rw [lpHaar_split_partition_union n _ _ (F.cell_split n), ih]

theorem cell_cover (n : ℕ) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ ⋃ k, F.cell n k := by
  rw [F.cell_union]
  exact lpHaarRootCell_ae

theorem cell_real_measure (n : ℕ) (k : Fin (2 ^ n)) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (F.cell n k) = intervalLpDyadicRadius n := by
  induction n with
  | zero =>
      rw [cell, lpHaarHeapIndex_zero, F.root_set, LpHaarFiniteParent.root_set,
        measureReal_def, lpHaarCell_measure 0 0 (by decide),
        ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos 0).le]
  | succ n ih =>
      obtain ⟨⟨j, b⟩, rfl⟩ := (lpHaarChildrenEquiv n).surjective k
      fin_cases b
      · change (volume.restrict (Icc (0 : ℝ) 1)).real
          (F.cell (n + 1) (lpHaarChildrenEquiv n (j, 0))) = _
        rw [lpHaarChildrenEquiv_left, F.cell_left, LpHaarFiniteSplit.child_mass]
        change (volume.restrict (Icc (0 : ℝ) 1)).real (F.cell n j) / 2 = _
        rw [ih, lpHaarRadius_succ]
      · change (volume.restrict (Icc (0 : ℝ) 1)).real
          (F.cell (n + 1) (lpHaarChildrenEquiv n (j, 1))) = _
        rw [lpHaarChildrenEquiv_right, F.cell_right, LpHaarFiniteSplit.child_mass]
        change (volume.restrict (Icc (0 : ℝ) 1)).real (F.cell n j) / 2 = _
        rw [ih, lpHaarRadius_succ]

def toPartitionTree : LpHaarPartitionTree where
  cell := F.cell
  measurable n k := (F.node (lpHaarHeapIndex n k)).parent.measurable
  disjoint := F.cell_disjoint
  cover := F.cell_cover
  measure n k := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _),
      ← measureReal_def, F.cell_real_measure]
  split := F.cell_split

theorem faithful : F.toPartitionTree.FaithfulSplits := by
  intro n k
  let S := F.node (lpHaarHeapIndex n k)
  refine ⟨S.level, S.atoms, S.signs,
    (lpHaarHeapIndex_depth_le n k).trans (F.level _), ?_, ?_⟩
  · change F.cell (n + 1) (lpHaarLeftIndex n k) = _
    rw [F.cell_left, LpHaarFiniteSplit.child_set]
    rfl
  · change F.cell (n + 1) (lpHaarRightIndex n k) = _
    rw [F.cell_right, LpHaarFiniteSplit.child_set]
    rfl

end LpHaarSequentialSplits
end ThesisCommon
