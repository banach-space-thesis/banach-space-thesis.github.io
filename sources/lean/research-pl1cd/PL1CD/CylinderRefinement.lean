import PL1.KernelTranslations

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace PL1CD.CylinderRefinement
open PL1.Walsh PL1.FiniteCoordinateKernels

def merge (S T : Finset ℕ) (a : Assignments S) (b : Assignments T) : PL1.Walsh.Group :=
  fun j => if hs : j ∈ S then a ⟨j, hs⟩ else if ht : j ∈ T then b ⟨j, ht⟩ else 1

theorem merge_left (S T : Finset ℕ) (a : Assignments S) (b : Assignments T) (j : S) :
    merge S T a b j = a j := by simp [merge]

theorem merge_right (S T : Finset ℕ) (hST : Disjoint S T)
    (a : Assignments S) (b : Assignments T) (j : T) : merge S T a b j = b j := by
  have hj : (j : ℕ) ∉ S := fun h => (Finset.disjoint_left.mp hST) h j.property
  simp [merge, hj]

def assignmentEquiv (S T : Finset ℕ) (hST : Disjoint S T) :
    Assignments (S ∪ T) ≃ Assignments S × Assignments T where
  toFun c := (fun j => c ⟨j, Finset.mem_union_left T j.property⟩,
    fun j => c ⟨j, Finset.mem_union_right S j.property⟩)
  invFun ab := fun j => merge S T ab.1 ab.2 j
  left_inv c := by
    funext j
    by_cases hs : (j : ℕ) ∈ S
    · simp [merge, hs]
    · have ht : (j : ℕ) ∈ T := (Finset.mem_union.mp j.property).resolve_left hs
      simp [merge, hs, ht]
  right_inv ab := by
    rcases ab with ⟨a, b⟩
    apply Prod.ext
    · funext j; exact merge_left S T a b j
    · funext j; exact merge_right S T hST a b j

theorem cylinder_merge_iff (S T : Finset ℕ) (hST : Disjoint S T)
    (a : Assignments S) (b : Assignments T) (y : PL1.Walsh.Group) :
    y ∈ cylinder (S ∪ T) (merge S T a b) ↔
      y ∈ cylinder S (extend S a) ∧ b = fun j : T => y j := by
  constructor
  · intro hy
    constructor
    · intro j hj
      exact (hy j (Finset.mem_union_left T hj)).trans
        ((merge_left S T a b ⟨j, hj⟩).trans (extend_apply S a ⟨j, hj⟩).symm)
    · funext j
      exact ((merge_right S T hST a b j).symm.trans
        (hy j (Finset.mem_union_right S j.property)).symm)
  · rintro ⟨ha, rfl⟩ j hj
    rcases Finset.mem_union.mp hj with hs | ht
    · exact (ha j hs).trans ((extend_apply S a ⟨j, hs⟩).trans
        (merge_left S T a _ ⟨j, hs⟩).symm)
    · exact (merge_right S T hST a (fun j : T => y j) ⟨j, ht⟩).symm

theorem sum_descendant_kernel (S T : Finset ℕ) (hST : Disjoint S T)
    (a : Assignments S) (y : PL1.Walsh.Group) :
    ∑ b : Assignments T, kernel (S ∪ T) (merge S T a b) y =
      (2 : ℝ) ^ T.card * kernel S (extend S a) y := by
  classical
  by_cases hy : y ∈ cylinder S (extend S a)
  · rw [Finset.sum_eq_single (fun j : T => y j)]
    · rw [kernel_eq_indicator, Set.indicator_of_mem
        ((cylinder_merge_iff S T hST a _ y).mpr ⟨hy, rfl⟩),
        kernel_eq_indicator, Set.indicator_of_mem hy, Finset.card_union_of_disjoint hST,
        pow_add, mul_comm]
    · intro b _ hb
      rw [kernel_eq_indicator, Set.indicator_of_notMem]
      exact fun h => hb ((cylinder_merge_iff S T hST a b y).mp h).2
    · simp
  · rw [kernel_eq_indicator, Set.indicator_of_notMem hy, mul_zero]
    apply Finset.sum_eq_zero
    intro b _
    rw [kernel_eq_indicator, Set.indicator_of_notMem]
    exact fun h => hy ((cylinder_merge_iff S T hST a b y).mp h).1

theorem mean_descendant_kernelL1 (S T : Finset ℕ) (hST : Disjoint S T)
    (a : Assignments S) :
    (Fintype.card (Assignments T) : ℝ)⁻¹ •
      (∑ b : Assignments T, kernelL1 (S ∪ T) (merge S T a b)) =
        kernelL1 S (extend S a) := by
  have he : (Fintype.card (Assignments T) : ℝ)⁻¹ •
      (∑ b : Assignments T, kernel (S ∪ T) (merge S T a b)) = kernel S (extend S a) := by
    ext y
    simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]
    rw [sum_descendant_kernel S T hST a y, card_assignments]
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have h := congrArg (ContinuousMap.toLp 1 haar ℝ) he
  simpa only [map_smul, map_sum, kernelL1] using h

theorem mean_operator_descendants {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : Lp ℝ 1 haar →L[ℝ] Z) (S T : Finset ℕ) (hST : Disjoint S T)
    (a : Assignments S) :
    (Fintype.card (Assignments T) : ℝ)⁻¹ •
      (∑ b : Assignments T, B (kernelL1 (S ∪ T) (merge S T a b))) =
        B (kernelL1 S (extend S a)) := by
  rw [← map_sum, ← map_smul, mean_descendant_kernelL1 S T hST a]

end PL1CD.CylinderRefinement
