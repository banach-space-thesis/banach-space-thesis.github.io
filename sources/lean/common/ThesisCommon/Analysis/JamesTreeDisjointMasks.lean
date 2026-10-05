import ThesisCommon.Analysis.JamesTreeMasks
import ThesisCommon.Analysis.FinitePiLpNormSuprema

/-! Genuine finite disjoint coordinate masks have a contractive joint lp
norm. The proof combines their actual disjoint segment tests and then
takes each norming supremum. It applies to both segment conventions. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}
  {ι : Type*} [Fintype ι]

namespace JamesTreePreSpace

theorem disjoint_mask_tests_norm_le (hp : 0 < p.val.toReal)
    (A : ι → Set DyadicTreeNode) (hA : ∀ i, JamesTreeMaskClosed S (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (a : JamesTreePreSpace 𝕜 p S) (T : ι → JamesTreeTest S) :
    ‖WithLp.toLp p.val (fun i => ‖jamesTreeTestMap 𝕜 p (T i)
      (coefficients (mask (A i) (hA i) a))‖)‖ ≤ ‖a‖ := by
  classical
  rw [piLp_norm_norms_eq_sigma p hp]
  let B : (i : ι) × Fin (T i).count → Finset DyadicTreeNode :=
    fun q => ((T q.1).segment q.2).filter (· ∈ A q.1)
  have hB : ∀ q, (B q).Nonempty → S.allows (B q) :=
    fun q => hA q.1 _ ((T q.1).allowed q.2)
  have hBd : Pairwise (fun q r => Disjoint (B q) (B r)) := by
    rintro ⟨i,j⟩ ⟨k,l⟩ hne
    by_cases hik : i=k
    · subst k
      exact ((T i).disjoint (fun hjl => hne (by cases hjl; rfl))).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · apply Finset.disjoint_left.mpr
      intro t ht hu
      exact Set.disjoint_left.mp (hd hik) (Finset.mem_filter.mp ht).2
        (Finset.mem_filter.mp hu).2
  have hb := jamesTree_partial_test_norm_le p a B hB hBd
  convert hb using 1
  congr 1
  ext q
  change (∑ t ∈ (T q.1).segment q.2, if t ∈ A q.1 then a t else 0) =
    ∑ t ∈ ((T q.1).segment q.2).filter (· ∈ A q.1), a t
  rw [Finset.sum_filter]

theorem disjoint_masks_norm_le (hp : 0 < p.val.toReal)
    (A : ι → Set DyadicTreeNode) (hA : ∀ i, JamesTreeMaskClosed S (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (a : JamesTreePreSpace 𝕜 p S) :
    ‖WithLp.toLp p.val (fun i => ‖mask (A i) (hA i) a‖)‖ ≤ ‖a‖ := by
  simp_rw [norm_def]
  apply piLp_norm_ciSup_le p
  · intro i
    exact testNorms_bddAbove _
  · exact disjoint_mask_tests_norm_le hp A hA hd a

end JamesTreePreSpace

theorem jamesTree_disjoint_masks_norm_le (hp : 0 < p.val.toReal)
    (A : ι → Set DyadicTreeNode) (hA : ∀ i, JamesTreeMaskClosed S (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖WithLp.toLp p.val (fun i => ‖jamesTreeMask (A i) (hA i) x‖)‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · apply isClosed_le _ continuous_norm
    apply Continuous.norm
    apply (PiLp.continuous_toLp p.val (fun _ : ι => ℝ)).comp
    exact continuous_pi (fun i => (jamesTreeMask (A i) (hA i)).continuous.norm)
  · intro a
    simp only [jamesTreeMask_dense,jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.disjoint_masks_norm_le hp A hA hd a

theorem jamesTree_disjoint_masks_sum_rpow_le (hp : 0 < p.val.toReal)
    (A : ι → Set DyadicTreeNode) (hA : ∀ i, JamesTreeMaskClosed S (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    ∑ i, ‖jamesTreeMask (A i) (hA i) x‖ ^ p.val.toReal ≤ ‖x‖ ^ p.val.toReal := by
  have hh := Real.rpow_le_rpow (norm_nonneg _)
    (jamesTree_disjoint_masks_norm_le hp A hA hd x) hp.le
  rw [PiLp.norm_eq_sum hp,one_div,
    Real.rpow_inv_rpow (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)) hp.ne'] at hh
  change ∑ i, ‖‖jamesTreeMask (A i) (hA i) x‖‖ ^ p.val.toReal ≤ ‖x‖ ^ p.val.toReal at hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hh

end ThesisCommon
