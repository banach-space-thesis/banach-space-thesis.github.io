import SurveyStatements.P5BiTreeStabilizationDefinitions
import SurveyStatements.P5BiTreeStabilizationHistory

/-! A whole-level recursive signed tree, and its exact conversion to the
checked sequential signed tree used by the faithful retraction modules. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal Classical

namespace SurveyStatements.P5.BiTree
open P5Support

abbrev LevelSplits (n : ℕ) := Fin (2 ^ n) → LpHaarFiniteSplit
abbrev LevelPairs (n : ℕ) := LevelSplits n × LevelSplits n

def historyParents : (n : ℕ) → ((i : Fin n) → LevelSplits i.val) →
    Fin (2 ^ n) → LpHaarFiniteParent
  | 0, _, _ => LpHaarFiniteParent.root
  | n + 1, h, k =>
      ((h ⟨n, Nat.lt_succ_self n⟩) ((lpHaarChildrenEquiv n).symm k).1).child
        (decide (((lpHaarChildrenEquiv n).symm k).2 = 0))

theorem historyParents_left (n : ℕ) (h : (i : Fin (n + 1)) → LevelSplits i.val)
    (k : Fin (2 ^ n)) :
    historyParents (n + 1) h (lpHaarLeftIndex n k) =
      ((h ⟨n, Nat.lt_succ_self n⟩) k).child true := by
  rw [← lpHaarChildrenEquiv_left]
  simp only [historyParents, Equiv.symm_apply_apply, decide_true]

theorem historyParents_right (n : ℕ) (h : (i : Fin (n + 1)) → LevelSplits i.val)
    (k : Fin (2 ^ n)) :
    historyParents (n + 1) h (lpHaarRightIndex n k) =
      ((h ⟨n, Nat.lt_succ_self n⟩) k).child false := by
  rw [← lpHaarChildrenEquiv_right]
  simp only [historyParents, Equiv.symm_apply_apply]
  rfl

def heapDecode (j : ℕ) : DyadicIndex :=
  ⟨(j + 1).log2, ⟨j + 1 - 2 ^ (j + 1).log2, lpHaar_remainder_lt (j + 1)⟩⟩

theorem heapIndex_decode (j : ℕ) :
    lpHaarHeapIndex (heapDecode j).1 (heapDecode j).2 = j := by
  have hp := lpHaar_pow_log2_le (i := j + 1) (by omega)
  simp only [heapDecode, lpHaarHeapIndex]
  omega

theorem heapDecode_index (n : ℕ) (k : Fin (2 ^ n)) :
    heapDecode (lpHaarHeapIndex n k) = ⟨n, k⟩ := by
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  have hj : lpHaarHeapIndex n k + 1 = 2 ^ n + k.val := by
    unfold lpHaarHeapIndex
    omega
  have hlog := lpHaar_log2_index n k
  have hlog' : (lpHaarHeapIndex n k + 1).log2 = n := by rw [hj]; exact hlog
  unfold heapDecode
  apply Sigma.ext hlog'
  apply (Fin.heq_ext_iff (congrArg (fun m : ℕ => 2 ^ m) hlog')).mpr
  simp only [hlog']
  omega

theorem heapIndex_injective :
    Function.Injective (fun I : DyadicIndex => lpHaarHeapIndex I.1 I.2) := by
  intro I J h
  have he := congrArg heapDecode h
  simpa only [heapDecode_index] using he

theorem heapDecode_left (j : ℕ) : heapDecode (2 * j + 1) = child (heapDecode j) true := by
  apply heapIndex_injective
  change lpHaarHeapIndex (heapDecode (2 * j + 1)).1 (heapDecode (2 * j + 1)).2 = _
  rw [heapIndex_decode]
  change 2 * j + 1 = lpHaarHeapIndex ((heapDecode j).1 + 1)
    (lpHaarLeftIndex (heapDecode j).1 (heapDecode j).2)
  rw [lpHaarHeapIndex_left, heapIndex_decode]

theorem heapDecode_right (j : ℕ) : heapDecode (2 * j + 2) = child (heapDecode j) false := by
  apply heapIndex_injective
  change lpHaarHeapIndex (heapDecode (2 * j + 2)).1 (heapDecode (2 * j + 2)).2 = _
  rw [heapIndex_decode]
  change 2 * j + 2 = lpHaarHeapIndex ((heapDecode j).1 + 1)
    (lpHaarRightIndex (heapDecode j).1 (heapDecode j).2)
  rw [lpHaarHeapIndex_right, heapIndex_decode]

theorem heapDecode_zero : heapDecode 0 = root := by
  simpa only [lpHaarHeapIndex_zero] using heapDecode_index 0 ⟨0, by decide⟩

structure DyadicSignedTree where
  node : DyadicIndex → LpHaarFiniteSplit
  level : ∀ I, lpHaarHeapIndex I.1 I.2 ≤ (node I).level
  root : (node root).parent.set = LpHaarFiniteParent.root.set
  children : ∀ I b, (node (child I b)).parent.set = ((node I).child b).set

def DyadicSignedTree.toSequentialSplits (F : DyadicSignedTree) : SignedTree where
  node j := F.node (heapDecode j)
  level j := by simpa only [heapIndex_decode] using F.level (heapDecode j)
  parent j := by
    by_cases hj : j = 0
    · subst j
      simpa only [lpHaarHistoryParent, dif_pos rfl, heapDecode_zero] using F.root
    · rw [lpHaarHistoryParent, dif_neg hj]
      let q := (j - 1) / 2
      change (F.node (heapDecode j)).parent.set =
        ((F.node (heapDecode q)).child (decide (j % 2 = 1))).set
      by_cases hmod : j % 2 = 1
      · have hodd : j = 2 * q + 1 := by dsimp only [q]; omega
        have he : heapDecode j = child (heapDecode q) true := by
          rw [hodd, heapDecode_left]
        have hdec : decide (j % 2 = 1) = true := by simp [hmod]
        rw [he, hdec]
        exact F.children _ _
      · have heven : j = 2 * q + 2 := by dsimp only [q]; omega
        have he : heapDecode j = child (heapDecode q) false := by
          rw [heven, heapDecode_right]
        have hdec : decide (j % 2 = 1) = false := by simp [hmod]
        rw [he, hdec]
        exact F.children _ _

theorem DyadicSignedTree.toSequentialSplits_block (F : DyadicSignedTree) (I : DyadicIndex) :
    F.toSequentialSplits.block I = F.node I := by
  simp only [SignedTree.block, DyadicSignedTree.toSequentialSplits, heapDecode_index]

end SurveyStatements.P5.BiTree
