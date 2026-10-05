import JFA.CZeroDiscreteTensor
import JLMS.DisjointSynthesis

/-! Disjoint synthesis over any discrete index set. This extends the checked
JLMS null-sequence construction to finite or countable subfamilies without
assuming that the subfamily is infinite. -/

noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι K : Type*} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace K]
local instance disjointCzeroSynthesisDecidableEq : DecidableEq ι := Classical.decEq ι
variable (η : ι → C₀(K, 𝕜)) (hunit : ∀ i, ‖η i‖ ≤ 1)
  (hd : Pairwise fun i j => Disjoint (Function.support (η i)) (Function.support (η j)))

omit [TopologicalSpace ι] [DiscreteTopology ι] in
include hunit hd in
theorem norm_sum_smul_disjointCzero_le (s : Finset ι) (a : ι → 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ i ∈ s, ‖a i‖ ≤ C) : ‖∑ i ∈ s, a i • η i‖ ≤ C := by
  classical
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro x
  change ‖JLMS.evaluation (𝕜 := 𝕜) x (∑ i ∈ s, a i • η i)‖ ≤ C
  simp only [map_sum, map_smul, JLMS.evaluation_apply, smul_eq_mul]
  by_cases hx : ∃ i ∈ s, η i x ≠ 0
  · obtain ⟨i, hi, hix⟩ := hx
    rw [Finset.sum_eq_single i]
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left ((JLMS.norm_CZero_apply_le (η i) x).trans (hunit i))
        (norm_nonneg _)).trans (by simpa using ha i hi)
    · intro j hj hji
      have hjzero : η j x = 0 := by
        by_contra hjx
        exact Set.disjoint_left.mp (hd hji) hjx hix
      rw [hjzero, mul_zero]
    · exact fun h => (h hi).elim
  · push_neg at hx
    rw [Finset.sum_eq_zero (fun i hi => by rw [hx i hi, mul_zero]), norm_zero]
    exact hC

include hunit hd in
theorem summable_smul_disjointCzero (a : C₀(ι, 𝕜)) : Summable (fun i => a i • η i) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hev := Metric.tendsto_nhds.mp a.zero_at_infty' (ε / 2) (half_pos hε)
  rw [cocompact_eq_cofinite] at hev
  have hbad : {i : ι | ¬ ‖a i‖ < ε / 2}.Finite := by
    simpa only [dist_zero_right] using mem_cofinite.mp hev
  classical
  refine ⟨hbad.toFinset, ?_⟩
  intro t ht
  apply lt_of_le_of_lt (norm_sum_smul_disjointCzero_le η hunit hd t a (half_pos hε).le ?_)
    (half_lt_self hε)
  intro i hi
  have hinot : i ∉ hbad.toFinset := fun h => Finset.disjoint_left.mp ht hi h
  have hsmall : ‖a i‖ < ε / 2 := by simpa using hinot
  exact hsmall.le

include hunit hd in
theorem norm_tsum_smul_disjointCzero_le (a : C₀(ι, 𝕜)) : ‖∑' i, a i • η i‖ ≤ ‖a‖ :=
  le_of_tendsto (summable_smul_disjointCzero η hunit hd a).hasSum.norm
    (Eventually.of_forall (fun s => norm_sum_smul_disjointCzero_le η hunit hd s a (norm_nonneg a)
      (fun i _ => JLMS.norm_CZero_apply_le a i)))

def disjointCzeroSynthesis : C₀(ι, 𝕜) →L[𝕜] C₀(K, 𝕜) :=
  ({ toFun a := ∑' i, a i • η i
     map_add' a b := by
       change (∑' i, (a i + b i) • η i) = _
       simp_rw [add_smul]
       exact (summable_smul_disjointCzero η hunit hd a).tsum_add
         (summable_smul_disjointCzero η hunit hd b)
     map_smul' c a := by
       change (∑' i, (c * a i) • η i) = c • _
       simp_rw [mul_smul]
       exact (summable_smul_disjointCzero η hunit hd a).tsum_const_smul c } :
      C₀(ι, 𝕜) →ₗ[𝕜] C₀(K, 𝕜)).mkContinuous 1
        (fun a => by simpa using norm_tsum_smul_disjointCzero_le η hunit hd a)

theorem norm_disjointCzeroSynthesis_le : ‖disjointCzeroSynthesis η hunit hd‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simpa using norm_tsum_smul_disjointCzero_le η hunit hd a

theorem disjointCzeroSynthesis_apply (a : C₀(ι, 𝕜)) (p : K) :
    disjointCzeroSynthesis η hunit hd a p = ∑' i, a i * η i p := by
  change JLMS.evaluation p (∑' i, a i • η i) = _
  rw [(JLMS.evaluation p).map_tsum (summable_smul_disjointCzero η hunit hd a)]
  simp only [map_smul, JLMS.evaluation_apply, smul_eq_mul]

theorem disjointCzeroSynthesis_apply_zero (a : C₀(ι, 𝕜)) (p : K)
    (hp : ∀ i, η i p = 0) : disjointCzeroSynthesis η hunit hd a p = 0 := by
  rw [disjointCzeroSynthesis_apply]
  simp only [hp, mul_zero, tsum_zero]

theorem disjointCzeroSynthesis_apply_coordinate (a : C₀(ι, 𝕜)) (p : K) (j : ι)
    (hp : ∀ i, η i p = if i = j then 1 else 0) :
    disjointCzeroSynthesis η hunit hd a p = a j := by
  classical
  rw [disjointCzeroSynthesis_apply]
  simp only [hp]
  rw [tsum_eq_single j]
  · simp
  · intro i hi
    simp only [if_neg hi, mul_zero]

end JFA
