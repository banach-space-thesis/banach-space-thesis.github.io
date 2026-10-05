import ThesisCommon.Analysis.JamesTreeSelectedColumnCells
import ThesisCommon.Analysis.JamesTreeSelectedErrorBudget
import ThesisCommon.Analysis.JamesTreeDelayedDiagonalErrors

/-! The recursively selected actual columns have summable readback errors.
All off-diagonal and support hypotheses are discharged using the selected
cell geometry, before invoking the full-vector finite-coordinate estimate. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

namespace JamesTreeColumnFrontierRun
variable {d : DyadicDelayedFork}
  {Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S}
  {ε : ℕ → ℝ}
  {hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N)}
  {hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B}

theorem read_column_error_le (a : JamesTreeColumnFrontierRun d Q ε hL hB)
    (hfinite : ∀ v, jamesTreeMask (dyadicInitialLevels (d.fork v).length) (hL _)
      (Q (jamesTreeUnit (d.node v))) = Q (jamesTreeUnit (d.node v)))
    (hI : ∀ t, S.allows (dyadicTreeInterval [] t))
    (he : JamesTreeDelayedForkClosure S (d.comp a.tree))
    (hε : ∀ i, 0≤ε i) (i : ℕ) :
    ‖jamesTreeDelayedRead (d.comp a.tree) he
        (Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration i))))) -
      (∑ t∈dyadicTreeInterval [] (d.fork (a.tree (dyadicTreeEnumeration i))),
        jamesTreeCoordinate t (Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration i)))))) •
        jamesTreeUnit (dyadicTreeEnumeration i)‖ ≤ (dyadicColumnErrorRows i).card*(2*ε i) := by
  classical
  let x := Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration i))))
  let c : 𝕜 := ∑ t∈dyadicTreeInterval [] (d.fork (a.tree (dyadicTreeEnumeration i))),
    jamesTreeCoordinate t x
  apply jamesTree_delayedRead_error_norm_le hL (d.comp a.tree) he
    (dyadicColumnErrorRows i) (dyadicTreeEnumeration i) c x
  · intro t ht
    have hnot := Finset.notMem_union.mp ht
    have hidx : i+1≤dyadicTreeEnumeration.symm t :=
      Nat.le_of_not_gt (fun hh => hnot.1 ((mem_dyadicEnumerationInitial t (i+1)).mpr hh))
    have hz := a.later_cell_zero hfinite (Nat.lt_succ_self i) hidx hnot.2
    have hb := norm_jamesTreeCoordinate_delayedRead_le_intervalMask
      (d.comp a.tree) he hB t x
    have hcoord : jamesTreeCoordinate t (jamesTreeDelayedRead (d.comp a.tree) he x)=0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [norm_zero] using hb.trans_eq (congrArg norm hz)) (norm_nonneg _)
    have hne : t≠dyadicTreeEnumeration i := by
      intro hh; exact ht (hh ▸ dyadicColumnErrorRows_current i)
    simp only [map_sub,map_smul,jamesTreeCoordinate_unit,if_neg hne,smul_zero,hcoord,sub_zero]
  · have hd := norm_jamesTree_delayed_diagonal_discrepancy_le_head hL hI
      (d.comp a.tree) he (dyadicTreeEnumeration i) (a.state i).cutoff x
      (fun t ht hne => a.processed_fork_le_cutoff
        (by simpa only [Equiv.symm_apply_apply] using dyadicTreeEnumeration_strict_prefix_index ht hne))
    have hh := a.head_small i
    have hb : ‖jamesTreeCoordinate (dyadicTreeEnumeration i)
        (jamesTreeDelayedRead (d.comp a.tree) he x)-c‖ ≤ ε i := by
      rw [norm_sub_rev]
      exact hd.trans hh.le
    exact hb.trans (by linarith [hε i])
  · intro t ht hne
    have hb := norm_jamesTreeCoordinate_delayedRead_le_intervalMask
      (d.comp a.tree) he hB t x
    rcases Finset.mem_union.mp ht with ht | ht
    · have htidx := (mem_dyadicEnumerationInitial t (i+1)).mp ht
      have hine : dyadicTreeEnumeration.symm t≠i := by
        intro hh
        exact hne (by simpa only [Equiv.apply_symm_apply] using congrArg dyadicTreeEnumeration hh)
      have hi : dyadicTreeEnumeration.symm t < i := by omega
      exact (hb.trans (a.earlier_cell_small hi).le).trans (by linarith [hε i])
    · exact hb.trans (a.frontier_cell_small hfinite (Nat.lt_succ_self i) ht)

theorem read_column_error_budget
    (a : JamesTreeColumnFrontierRun d Q jamesTreePruningTolerance hL hB)
    (hfinite : ∀ v, jamesTreeMask (dyadicInitialLevels (d.fork v).length) (hL _)
      (Q (jamesTreeUnit (d.node v))) = Q (jamesTreeUnit (d.node v)))
    (hI : ∀ t, S.allows (dyadicTreeInterval [] t))
    (he : JamesTreeDelayedForkClosure S (d.comp a.tree)) (i : ℕ) :
    ‖jamesTreeDelayedRead (d.comp a.tree) he
        (Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration i))))) -
      (∑ t∈dyadicTreeInterval [] (d.fork (a.tree (dyadicTreeEnumeration i))),
        jamesTreeCoordinate t (Q (jamesTreeUnit (d.node (a.tree (dyadicTreeEnumeration i)))))) •
        jamesTreeUnit (dyadicTreeEnumeration i)‖ ≤ jamesTreeColumnErrorWeight (dyadicTreeEnumeration i) := by
  exact (a.read_column_error_le hfinite hI he (fun i => (jamesTreePruningTolerance_pos i).le) i).trans_eq
    (jamesTreePruningTolerance_budget i)

end JamesTreeColumnFrontierRun
end ThesisCommon
