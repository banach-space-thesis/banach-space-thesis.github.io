import ThesisCommon.Analysis.JamesTreeFiniteReadErrors
import ThesisCommon.Analysis.DyadicRootedCellSums

/-! The exact discrepancy between the full root-path coefficient and the
current readback cell is the parent root path. Its norm is controlled by
the genuine low-level projection when earlier forks lie below the cut. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTree_root_sum_norm_le_level
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hI : ∀ t, S.allows (dyadicTreeInterval [] t))
    (t : DyadicTreeNode) (N : ℕ) (ht : t.length ≤ N)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖∑ u ∈ dyadicTreeInterval [] t, jamesTreeCoordinate u x‖ ≤
      ‖jamesTreeMask (dyadicInitialLevels N) (hL N) x‖ := by
  have he : (∑ u ∈ dyadicTreeInterval [] t,
      jamesTreeCoordinate u (jamesTreeMask (dyadicInitialLevels N) (hL N) x)) =
      ∑ u ∈ dyadicTreeInterval [] t, jamesTreeCoordinate u x := by
    apply Finset.sum_congr rfl
    intro u hu
    have huN : u ∈ dyadicInitialLevels N :=
      (((mem_dyadicTreeInterval [] t u).mp hu).2.length_le).trans ht
    simp only [jamesTreeCoordinate_mask,if_pos huN]
  rw [←he]
  exact jamesTree_allowed_sum_norm_le _ (hI t) _

theorem norm_jamesTree_delayed_diagonal_discrepancy_le_head
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hI : ∀ t, S.allows (dyadicTreeInterval [] t))
    (d : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S d)
    (s : DyadicTreeNode) (N : ℕ) (x : SegmentJamesTreeSpace 𝕜 p S)
    (hN : ∀ t, t.IsPrefix s → t ≠ s → (d.fork t).length ≤ N) :
    ‖(∑ t ∈ dyadicTreeInterval [] (d.fork s), jamesTreeCoordinate t x) -
      jamesTreeCoordinate s (jamesTreeDelayedRead d hS x)‖ ≤
      ‖jamesTreeMask (dyadicInitialLevels N) (hL N) x‖ := by
  rw [jamesTreeCoordinate_delayedRead]
  induction s using List.reverseRecOn with
  | nil =>
    rw [dyadicRootedCell_full_sum_sub_nil,norm_zero]
    exact norm_nonneg _
  | append_singleton s b _ =>
    rw [dyadicRootedCell_full_sum_sub_snoc]
    apply jamesTree_root_sum_norm_le_level hL hI
    apply hN s (List.prefix_append s [b])
    intro h
    have hh := congrArg List.length h
    simp only [List.length_append,List.length_singleton] at hh
    omega

theorem norm_jamesTree_delayed_diagonal_discrepancy_le_head_of_processed
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hI : ∀ t, S.allows (dyadicTreeInterval [] t))
    (d : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S d)
    (s : DyadicTreeNode) (N : ℕ) (x : SegmentJamesTreeSpace 𝕜 p S)
    (hN : ∀ i, i < dyadicTreeEnumeration.symm s →
      (d.fork (dyadicTreeEnumeration i)).length ≤ N) :
    ‖(∑ t ∈ dyadicTreeInterval [] (d.fork s), jamesTreeCoordinate t x) -
      jamesTreeCoordinate s (jamesTreeDelayedRead d hS x)‖ ≤
      ‖jamesTreeMask (dyadicInitialLevels N) (hL N) x‖ := by
  apply norm_jamesTree_delayed_diagonal_discrepancy_le_head hL hI d hS s N x
  intro t hts hne
  simpa only [Equiv.apply_symm_apply] using
    hN (dyadicTreeEnumeration.symm t) (dyadicTreeEnumeration_strict_prefix_index hts hne)

end ThesisCommon
