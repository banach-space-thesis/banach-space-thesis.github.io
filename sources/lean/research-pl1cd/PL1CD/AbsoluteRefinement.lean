import PL1CD.HaarPartitionAlgebra
import PL1CD.RealL1FiniteOrder

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators

namespace PL1CD.HaarPartitions
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.PositiveHaarOperators PL1CD.L1Order
open PL1CD.CylinderRefinement

theorem restrict_assignmentEquiv_symm (S T V : Finset ℕ) (hST : Disjoint S T)
    (hVS : V ⊆ S) (a : Assignments S) (b : Assignments T) :
    restrict (S ∪ T) V (hVS.trans Finset.subset_union_left)
      ((assignmentEquiv S T hST).symm (a, b)) = restrict S V hVS a := by
  funext j
  exact merge_left S T a b ⟨j, hVS j.property⟩

theorem absoluteOperator_refinement_le (B : HaarL1 →L[ℝ] HaarL1)
    (S T V : Finset ℕ) (hST : Disjoint S T) (hVS : V ⊆ S) (c : Assignments V) :
    ∀ᵐ x ∂haar, absoluteOperator B S (atom V c) x ≤
      absoluteOperator B (S ∪ T) (atom V c) x := by
  rw [absoluteOperator_atom B S V hVS c,
    absoluteOperator_atom B (S ∪ T) V (hVS.trans Finset.subset_union_left) c]
  rw [← (assignmentEquiv S T hST).symm.sum_comp, Fintype.sum_prod_type]
  simp only [restrict_assignmentEquiv_symm S T V hST hVS]
  apply sum_ae_le_sum
  intro a
  by_cases ha : restrict S V hVS a = c
  · simp only [ha, if_true]
    rw [← sum_descendant_atom S T hST a, map_sum]
    exact absL1_sum_le_sum_absL1 Finset.univ
      (fun b : Assignments T => B (atom (S ∪ T) ((assignmentEquiv S T hST).symm (a, b))))
  · simp only [ha, if_false, Finset.sum_const_zero]
    exact ae_of_all _ (fun x => le_refl _)

theorem absoluteOperator_range_le_succ (B : HaarL1 →L[ℝ] HaarL1)
    (k r : ℕ) (hkr : k ≤ r) (a : Assignments (Finset.range k)) :
    ∀ᵐ x ∂haar, absoluteOperator B (Finset.range r) (atom (Finset.range k) a) x ≤
      absoluteOperator B (Finset.range (r + 1)) (atom (Finset.range k) a) x := by
  have hd : Disjoint (Finset.range r) {r} := by simp
  have he : Finset.range r ∪ {r} = Finset.range (r + 1) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton]
    omega
  simpa only [he] using absoluteOperator_refinement_le B (Finset.range r) {r}
    (Finset.range k) hd (Finset.range_mono hkr) a

theorem absoluteOperator_atom_has_limit (B : HaarL1 →L[ℝ] HaarL1)
    (k : ℕ) (a : Assignments (Finset.range k)) :
    ∃ g : HaarL1, Tendsto
      (fun r => absoluteOperator B (Finset.range (k + r)) (atom (Finset.range k) a))
      atTop (𝓝 g) := by
  let f : ℕ → HaarL1 := fun r =>
    absoluteOperator B (Finset.range (k + r)) (atom (Finset.range k) a)
  have hp (r : ℕ) : Nonneg (f r) :=
    absoluteOperator_positive B _ _ (atom_nonneg _ a)
  have hm : ∀ᵐ x ∂haar, Monotone (fun r => f r x) := by
    have hs (r : ℕ) : ∀ᵐ x ∂haar, f r x ≤ f (r + 1) x := by
      simpa only [f, Nat.add_assoc] using
        absoluteOperator_range_le_succ B k (k + r) (by omega) a
    filter_upwards [ae_all_iff.mpr hs] with x hx
    exact monotone_nat_of_le_succ hx
  obtain ⟨g, _, ht, _, _⟩ := exists_L1_limit_of_monotone f hp hm
    (‖B‖ * ‖atom (Finset.range k) a‖) (fun r =>
      ((absoluteOperator B _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_absoluteOperator_le B _) (norm_nonneg _)))
  exact ⟨g, ht⟩

end PL1CD.HaarPartitions
