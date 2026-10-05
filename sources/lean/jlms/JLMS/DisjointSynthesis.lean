import JLMS.CZeroIdentity
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Synthesizing c₀ from disjoint unit-ball functions

The finite sums have norm bounded by the largest coefficient, because
only one disjoint function can be nonzero at any point. Vanishing c₀
coefficients then give uniform convergence. This constructs the operator
V in the factorization bridge, with norm at most one.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]
variable (η : ℕ → CZero 𝕜 K) (hunit : ∀ n, ‖η n‖ ≤ 1)
    (hdisjoint : Pairwise fun i j => Disjoint (Function.support (η i)) (Function.support (η j)))

include hunit hdisjoint

/-- The supremum estimate for a finite disjoint linear combination. -/
theorem norm_sum_smul_disjoint_le (s : Finset ℕ) (a : ℕ → 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n ∈ s, ‖a n‖ ≤ C) :
    ‖∑ n ∈ s, a n • η n‖ ≤ C := by
  classical
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro x
  change ‖evaluation (𝕜 := 𝕜) x (∑ n ∈ s, a n • η n)‖ ≤ C
  simp only [map_sum, map_smul, evaluation_apply, smul_eq_mul]
  by_cases hx : ∃ n ∈ s, η n x ≠ 0
  · obtain ⟨n, hn, hx⟩ := hx
    rw [Finset.sum_eq_single n]
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left ((norm_CZero_apply_le (η n) x).trans (hunit n))
        (norm_nonneg _)).trans (by simpa using ha n hn)
    · intro m hm hmn
      have hmzero : η m x = 0 := by
        by_contra hmx
        exact Set.disjoint_left.mp (hdisjoint hmn) hmx hx
      rw [hmzero, mul_zero]
    · exact fun h => (h hn).elim
  · push_neg at hx
    rw [Finset.sum_eq_zero (fun n hn => by rw [hx n hn, mul_zero]), norm_zero]
    exact hC

/-- The disjoint synthesis series converges uniformly for every c₀ coefficient vector. -/
theorem summable_smul_disjoint (a : cZero 𝕜) : Summable (fun n => a n • η n) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hev := Metric.tendsto_nhds.mp a.zero_at_infty' (ε / 2) (half_pos hε)
  rw [cocompact_eq_cofinite] at hev
  have hbad : {n : ℕ | ¬ ‖a n‖ < ε / 2}.Finite := by
    simpa only [dist_zero_right] using mem_cofinite.mp hev
  refine ⟨hbad.toFinset, ?_⟩
  intro t ht
  apply lt_of_le_of_lt (norm_sum_smul_disjoint_le η hunit hdisjoint t a (half_pos hε).le ?_)
    (half_lt_self hε)
  intro n hn
  have hnnot : n ∉ hbad.toFinset := fun h => Finset.disjoint_left.mp ht hn h
  have hsmall : ‖a n‖ < ε / 2 := by simpa using hnnot
  exact hsmall.le

/-- Uniform norm control of the infinite disjoint combination. -/
theorem norm_tsum_smul_disjoint_le (a : cZero 𝕜) : ‖∑' n, a n • η n‖ ≤ ‖a‖ := by
  exact le_of_tendsto (summable_smul_disjoint η hunit hdisjoint a).hasSum.norm
    (Eventually.of_forall (fun s => norm_sum_smul_disjoint_le η hunit hdisjoint s a (norm_nonneg a)
      (fun n _ => norm_CZero_apply_le a n)))

/-- The contraction V:c₀→C₀(K) associated with a disjoint unit-ball sequence. -/
def disjointSynthesis : cZero 𝕜 →L[𝕜] CZero 𝕜 K :=
  ({ toFun a := ∑' n, a n • η n
     map_add' a b := by
       change (∑' n, (a n + b n) • η n) = _
       simp_rw [add_smul]
       exact (summable_smul_disjoint η hunit hdisjoint a).tsum_add
         (summable_smul_disjoint η hunit hdisjoint b)
     map_smul' c a := by
       change (∑' n, (c * a n) • η n) = c • _
       simp_rw [mul_smul]
       exact (summable_smul_disjoint η hunit hdisjoint a).tsum_const_smul c } :
      cZero 𝕜 →ₗ[𝕜] CZero 𝕜 K).mkContinuous 1
        (fun a => by simpa using norm_tsum_smul_disjoint_le η hunit hdisjoint a)

theorem norm_disjointSynthesis_le : ‖disjointSynthesis η hunit hdisjoint‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simpa using norm_tsum_smul_disjoint_le η hunit hdisjoint a

@[simp] theorem disjointSynthesis_unit (n : ℕ) :
    disjointSynthesis η hunit hdisjoint (cZeroUnit 𝕜 n) = η n := by
  classical
  change (∑' m, cZeroUnit 𝕜 n m • η m) = η n
  rw [tsum_eq_single n]
  · simp
  · intro m hmn
    simp [hmn]

end JLMS
