import SurveyStatements.P5L1VariationLocalTree
import SurveyStatements.P5L1VariationTreeCoordinates

/-! Concrete independent child flips. The chosen Haar vector changes sign;
earlier Haar vectors and the other vectors of its level stay fixed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem xor_one_even (k : ℕ) : (2 * k) ^^^ 1 = 2 * k + 1 := by
  have hd : ((2 * k) ^^^ 1) / 2 = k := by rw [Nat.xor_div_two]; simp
  have hm : ((2 * k) ^^^ 1) % 2 = 1 := by simp
  omega

theorem xor_one_odd (k : ℕ) : (2 * k + 1) ^^^ 1 = 2 * k := by
  have hd : ((2 * k + 1) ^^^ 1) / 2 = k := by rw [Nat.xor_div_two]; simp; omega
  have hm : ((2 * k + 1) ^^^ 1) % 2 ≠ 1 := by simp
  have hb := Nat.mod_lt ((2 * k + 1) ^^^ 1) (by omega : 0 < 2)
  omega

def childFlipMask (M n : ℕ) (hn : n + 1 ≤ M) : Fin (2 ^ M) :=
  ⟨2 ^ (M - (n + 1)), Nat.pow_lt_pow_right (by norm_num) (by omega)⟩

theorem childFlipMask_lt (M n : ℕ) (hn : n + 1 ≤ M) :
    (childFlipMask M n hn).val < 2 ^ (M - n) :=
  Nat.pow_lt_pow_right (by norm_num) (by omega)

def childFlip (M n : ℕ) (hn : n + 1 ≤ M) (k : Fin (2 ^ n)) : DyadicTreePerm M :=
  localXorTreePermutation M n (by omega) k (childFlipMask M n hn) (childFlipMask_lt M n hn)

theorem childFlip_coarse_node (M n m : ℕ) (hn : n + 1 ≤ M) (hm : m ≤ n)
    (k : Fin (2 ^ n)) (j : Fin (2 ^ m)) :
    nodeAction (childFlip M n hn k) m (by omega) j = j := by
  apply Fin.ext
  let a := prefixLift M m (by omega) j
  have hmask : (childFlipMask M n hn).val < 2 ^ (M - m) :=
    (childFlipMask_lt M n hn).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  change (localXorLeaf M n k (childFlipMask M n hn) a).val / 2 ^ (M - m) = j.val
  by_cases ha : a.val / 2 ^ (M - n) = k.val
  · rw [localXorLeaf, if_pos ha, Nat.xor_div_two_pow, Nat.div_eq_of_lt hmask, Nat.xor_zero]
    exact congrArg Fin.val (prefixIndex_lift M m (by omega) j)
  · rw [localXorLeaf, if_neg ha]
    exact congrArg Fin.val (prefixIndex_lift M m (by omega) j)

theorem childFlip_left_node (M n : ℕ) (hn : n + 1 ≤ M) (k : Fin (2 ^ n)) :
    nodeAction (childFlip M n hn k) (n + 1) hn (lpHaarLeftIndex n k) =
      lpHaarRightIndex n k := by
  apply Fin.ext
  let a := prefixLift M (n + 1) hn (lpHaarLeftIndex n k)
  have ha : a.val / 2 ^ (M - n) = k.val := by
    have h := prefixLift_parent M n hn (lpHaarLeftIndex n k)
    have hp : lpHaarParentIndex n (lpHaarLeftIndex n k) = k := by
      apply Fin.ext
      simp [lpHaarParentIndex, lpHaarLeftIndex, lpHaarSignedChildIndex]
    rw [hp] at h
    exact congrArg Fin.val h
  change (localXorLeaf M n k (childFlipMask M n hn) a).val / 2 ^ (M - (n + 1)) = _
  rw [localXorLeaf, if_pos ha, Nat.xor_div_two_pow]
  have hprefix := congrArg Fin.val (prefixIndex_lift M (n + 1) hn (lpHaarLeftIndex n k))
  change a.val / 2 ^ (M - (n + 1)) = 2 * k.val at hprefix
  rw [hprefix]
  change (2 * k.val) ^^^ (2 ^ (M - (n + 1)) / 2 ^ (M - (n + 1))) = 2 * k.val + 1
  rw [Nat.div_self (by positivity), xor_one_even]

theorem childFlip_right_node (M n : ℕ) (hn : n + 1 ≤ M) (k : Fin (2 ^ n)) :
    nodeAction (childFlip M n hn k) (n + 1) hn (lpHaarRightIndex n k) =
      lpHaarLeftIndex n k := by
  have hp := nodeAction_parent (childFlip M n hn k) n hn (lpHaarRightIndex n k)
  have hparent : lpHaarParentIndex n (lpHaarRightIndex n k) = k := by
    apply Fin.ext
    change (2 * k.val + 1) / 2 = k.val
    omega
  rw [hparent, childFlip_coarse_node M n n hn le_rfl] at hp
  have hne : nodeAction (childFlip M n hn k) (n + 1) hn (lpHaarRightIndex n k) ≠
      lpHaarRightIndex n k := by
    intro h
    have hL := childFlip_left_node M n hn k
    exact lpHaar_child_indices_ne n k
      ((nodeAction_injective (childFlip M n hn k) (n + 1) hn) (hL.trans h.symm))
  apply Fin.ext
  have hd := congrArg Fin.val hp
  change (nodeAction (childFlip M n hn k) (n + 1) hn (lpHaarRightIndex n k)).val / 2 = k.val at hd
  have hnv : (nodeAction (childFlip M n hn k) (n + 1) hn (lpHaarRightIndex n k)).val ≠
      2 * k.val + 1 := fun h => hne (Fin.ext h)
  change _ = 2 * k.val
  omega

theorem childFlip_haar_neg (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n + 1 ≤ M) (k : Fin (2 ^ n)) :
    terminalPermutation 𝕜 M (childFlip M n hn k).val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      -lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  change terminalPermutation 𝕜 M (childFlip M n hn k).val
    (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarLeftIndex n k) -
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarRightIndex n k)) = _
  rw [map_sub, terminalPermutation_cell 𝕜 M (n + 1) hn,
    terminalPermutation_cell 𝕜 M (n + 1) hn,
    childFlip_left_node, childFlip_right_node]
  change _ = -(lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarLeftIndex n k) -
    lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarRightIndex n k))
  abel

theorem childFlip_earlier_haar (𝕜 : Type*) [RCLike 𝕜]
    (M n m : ℕ) (hn : n + 1 ≤ M) (hm : m < n)
    (k : Fin (2 ^ n)) (j : Fin (2 ^ m)) :
    terminalPermutation 𝕜 M (childFlip M n hn k).val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ m j) =
      lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ m j := by
  change terminalPermutation 𝕜 M (childFlip M n hn k).val
    (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (m + 1) (lpHaarLeftIndex m j) -
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (m + 1) (lpHaarRightIndex m j)) = _
  rw [map_sub, terminalPermutation_cell 𝕜 M (m + 1) (by omega),
    terminalPermutation_cell 𝕜 M (m + 1) (by omega),
    childFlip_coarse_node M n (m + 1) hn (by omega),
    childFlip_coarse_node M n (m + 1) hn (by omega)]
  rfl

theorem childFlip_other_children (M n : ℕ) (hn : n + 1 ≤ M)
    (k j : Fin (2 ^ n)) (hj : j ≠ k) (a : Fin (2 ^ (n + 1)))
    (ha : lpHaarParentIndex n a = j) :
    nodeAction (childFlip M n hn k) (n + 1) hn a = a := by
  let z := prefixLift M (n + 1) hn a
  have hz : z.val / 2 ^ (M - n) ≠ k.val := by
    have hp := prefixLift_parent M n hn a
    rw [ha] at hp
    intro h
    exact hj ((Fin.ext (congrArg Fin.val hp).symm).trans (Fin.ext h))
  change prefixIndex M (n + 1) hn (localXorLeaf M n k (childFlipMask M n hn) z) = a
  rw [localXorLeaf, if_neg hz]
  exact prefixIndex_lift M (n + 1) hn a

theorem childFlip_other_haar (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n + 1 ≤ M) (k j : Fin (2 ^ n)) (hj : j ≠ k) :
    terminalPermutation 𝕜 M (childFlip M n hn k).val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n j) =
      lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n j := by
  change terminalPermutation 𝕜 M (childFlip M n hn k).val
    (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarLeftIndex n j) -
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarRightIndex n j)) = _
  rw [map_sub, terminalPermutation_cell 𝕜 M (n + 1) hn,
    terminalPermutation_cell 𝕜 M (n + 1) hn]
  have hpL : lpHaarParentIndex n (lpHaarLeftIndex n j) = j := by
    apply Fin.ext
    simp [lpHaarParentIndex, lpHaarLeftIndex, lpHaarSignedChildIndex]
  have hpR : lpHaarParentIndex n (lpHaarRightIndex n j) = j := by
    apply Fin.ext
    change (2 * j.val + 1) / 2 = j.val
    omega
  rw [childFlip_other_children M n hn k j hj _ hpL,
    childFlip_other_children M n hn k j hj _ hpR]
  rfl

theorem childFlip_mem_local (M n r : ℕ) (hn : n + 1 ≤ M) (hr : r ≤ n)
    (root : Fin (2 ^ r)) (k : Fin (2 ^ n)) (hk : prefixIndex n r hr k = root) :
    childFlip M n hn k ∈ localDyadicTreeGroup M r (by omega) root := by
  intro a ha
  have hnot : a.val / 2 ^ (M - n) ≠ k.val := by
    intro h
    have heq : prefixIndex M n (by omega) a = k := Fin.ext h
    have hcomp := prefixIndex_comp M n r (by omega) hr a
    rw [heq, hk] at hcomp
    exact ha hcomp.symm
  change localXorLeaf M n k (childFlipMask M n hn) a = a
  rw [localXorLeaf, if_neg hnot]

end SurveyStatements.P5L1Variation
