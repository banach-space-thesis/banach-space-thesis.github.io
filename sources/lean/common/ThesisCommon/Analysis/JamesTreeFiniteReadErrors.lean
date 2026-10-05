import ThesisCommon.Analysis.JamesTreeDelayedCoordinates
import ThesisCommon.Analysis.JamesTreeMultiplierEstimates
import ThesisCommon.Analysis.JamesTreeFiniteLevels
import ThesisCommon.Analysis.DyadicCellAnchors
import ThesisCommon.Analysis.DyadicConePruningGeometry

/-! Full-vector finite-support reconstruction and error bounds for actual
delayed readback. All support and coordinate estimates are explicit; no
operator-preservation or factorization assertion is assumed. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTree_allowed_sum_norm_le (A : Finset DyadicTreeNode) (hA : S.allows A)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖∑ t ∈ A, jamesTreeCoordinate t x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (continuous_finset_sum _ (fun t _ => (jamesTreeCoordinate t).continuous)).norm
      continuous_norm
  · intro a
    simpa only [jamesTreeCoordinate_dense,jamesTreeDenseEmbedding_norm] using
      JamesTreePreSpace.segment_sum_norm_le A hA a

theorem jamesTree_eq_sum_coordinates_of_finite_support
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (A : Finset DyadicTreeNode) (y : SegmentJamesTreeSpace 𝕜 p S)
    (hy : ∀ t, t ∉ A → jamesTreeCoordinate t y = 0) :
    y = ∑ t ∈ A, jamesTreeCoordinate t y • jamesTreeUnit t := by
  classical
  apply jamesTreeCoordinate_ext hL
  intro s
  simp only [map_sum,map_smul,jamesTreeCoordinate_unit,smul_eq_mul]
  by_cases hs : s ∈ A
  · simp [mul_ite,hs]
  · simp [mul_ite,hs,hy s hs]

theorem jamesTree_norm_le_sum_coordinates_of_finite_support
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (A : Finset DyadicTreeNode) (y : SegmentJamesTreeSpace 𝕜 p S)
    (hy : ∀ t, t ∉ A → jamesTreeCoordinate t y = 0) :
    ‖y‖ ≤ ∑ t ∈ A, ‖jamesTreeCoordinate t y‖ := by
  calc
    _ = ‖∑ t ∈ A, jamesTreeCoordinate t y • jamesTreeUnit t‖ :=
      congrArg norm (jamesTree_eq_sum_coordinates_of_finite_support hL A y hy)
    _ ≤ ∑ t ∈ A, ‖jamesTreeCoordinate t y • jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) t‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_smul,norm_jamesTreeUnit,mul_one]

theorem jamesTree_norm_le_card_mul_of_finite_support
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (A : Finset DyadicTreeNode) (y : SegmentJamesTreeSpace 𝕜 p S)
    (hy : ∀ t, t ∉ A → jamesTreeCoordinate t y = 0) {η : ℝ}
    (hcoord : ∀ t ∈ A, ‖jamesTreeCoordinate t y‖ ≤ η) : ‖y‖ ≤ A.card * η := by
  exact (jamesTree_norm_le_sum_coordinates_of_finite_support hL A y hy).trans
    (by simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hcoord)

theorem norm_jamesTreeCoordinate_delayedRead_le_mask (d : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S d) (s : DyadicTreeNode)
    (hcell : JamesTreeMaskClosed S (dyadicRootedCell d.fork s : Set DyadicTreeNode))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreeCoordinate s (jamesTreeDelayedRead d hS x)‖ ≤
      ‖jamesTreeMask (dyadicRootedCell d.fork s : Set DyadicTreeNode) hcell x‖ := by
  classical
  have hallow : S.allows (dyadicRootedCell d.fork s) := by
    have heq : dyadicRootedCells d.fork {s} = dyadicRootedCell d.fork s := by
      ext t
      simp only [mem_dyadicRootedCells,Finset.mem_singleton,exists_eq_left]
    rw [←heq]
    exact hS.cells {s} (S.singleton_allowed s)
  rw [jamesTreeCoordinate_delayedRead]
  have he : (∑ t ∈ dyadicRootedCell d.fork s,
      jamesTreeCoordinate t (jamesTreeMask (dyadicRootedCell d.fork s : Set DyadicTreeNode) hcell x)) =
      ∑ t ∈ dyadicRootedCell d.fork s, jamesTreeCoordinate t x := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [jamesTreeCoordinate_mask]
    split_ifs with h
    · rfl
    · exact (h ht).elim
  rw [←he]
  exact jamesTree_allowed_sum_norm_le _ hallow _

theorem norm_jamesTreeCoordinate_delayedRead_le_intervalMask (d : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S d)
    (hB : ∀ B, IsConvexTreeChain B → JamesTreeMaskClosed S B)
    (s : DyadicTreeNode) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreeCoordinate s (jamesTreeDelayedRead d hS x)‖ ≤
      ‖jamesTreeMask (dyadicTreeInterval (dyadicCellAnchor d.fork s) (d.fork s) : Set DyadicTreeNode)
        (hB _ (dyadicTreeInterval_isConvex _ _)) x‖ := by
  have hcell : JamesTreeMaskClosed S (dyadicRootedCell d.fork s : Set DyadicTreeNode) := by
    rw [dyadicRootedCell_eq_interval]
    exact hB _ (dyadicTreeInterval_isConvex _ _)
  simpa only [dyadicRootedCell_eq_interval] using
    norm_jamesTreeCoordinate_delayedRead_le_mask d hS s hcell x

theorem jamesTree_delayedRead_error_norm_le
    (hL : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (d : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S d)
    (A : Finset DyadicTreeNode) (s : DyadicTreeNode) (c : 𝕜)
    (x : SegmentJamesTreeSpace 𝕜 p S) {η : ℝ}
    (hsupp : ∀ t, t ∉ A → jamesTreeCoordinate t
      (jamesTreeDelayedRead d hS x - c • jamesTreeUnit s) = 0)
    (hdiag : ‖jamesTreeCoordinate s (jamesTreeDelayedRead d hS x) - c‖ ≤ η)
    (hoff : ∀ t ∈ A, t ≠ s → ‖jamesTreeCoordinate t (jamesTreeDelayedRead d hS x)‖ ≤ η) :
    ‖jamesTreeDelayedRead d hS x - c • jamesTreeUnit s‖ ≤ A.card * η := by
  apply jamesTree_norm_le_card_mul_of_finite_support hL A _ hsupp
  intro t ht
  simp only [map_sub,map_smul,jamesTreeCoordinate_unit,smul_eq_mul]
  by_cases hts : t = s
  · subst t
    simpa only [ite_true,mul_one] using hdiag
  · simpa only [if_neg hts,mul_zero,sub_zero] using hoff t ht hts

end ThesisCommon
