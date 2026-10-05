import ThesisCommon.Analysis.CompactMetricPartition
import ThesisCommon.Analysis.FiniteWeightedDetection
import Mathlib.Topology.ContinuousMap.Algebra

/-! Continuous positive combinations of actual vectors, together with
explicit seminorm upper bounds and dual-functional lower bounds for
their operator images. The simultaneous vector/functional selection
needed in Lemma 9 remains a separate mathematical obligation. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 K ι V W : Type*} [RCLike 𝕜] [Fintype ι]
  [TopologicalSpace K] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

def partitionWeightedVector (p : ι → C(K, ℝ)) (v : ι → V) : C(K,V) where
  toFun x := ∑ i, ((p i x : ℝ) : 𝕜) • v i
  continuous_toFun := by
    apply continuous_finset_sum
    intro i _
    exact (RCLike.continuous_ofReal.comp (p i).continuous).smul continuous_const

theorem partitionWeightedVector_apply (p : ι → C(K, ℝ)) (v : ι → V) (x : K) :
    partitionWeightedVector (𝕜 := 𝕜) p v x = ∑ i, ((p i x : ℝ) : 𝕜) • v i := rfl

theorem seminorm_partitionWeightedVector_le
    (p : ι → C(K, ℝ)) (v : ι → V) (q : Seminorm 𝕜 V) {B : ℝ}
    (hp : ∀ i x, 0 ≤ p i x) (hs : ∀ x, ∑ i, p i x = 1)
    (hv : ∀ i, q (v i) ≤ B) (x : K) :
    q (partitionWeightedVector (𝕜 := 𝕜) p v x) ≤ B :=
  seminorm_positive_weighted_sum_le q (fun i => p i x) v (fun i => hp i x) (hs x) hv

theorem partitionWeightedVector_mem_submodule
    (p : ι → C(K, ℝ)) (v : ι → V) (E : Submodule 𝕜 V)
    (hv : ∀ i, v i ∈ E) (x : K) : partitionWeightedVector (𝕜 := 𝕜) p v x ∈ E := by
  exact E.sum_mem (fun i _ => E.smul_mem _ (hv i))

theorem norm_sub_operator_apply_gt_of_near
    (T A B : V →L[𝕜] W) (v : V) {r δ M : ℝ}
    (hδ : 0 ≤ δ) (hnear : ‖A-B‖ ≤ δ) (hv : ‖v‖ ≤ M)
    (hbad : r < ‖(T-A) v‖) : r-δ*M < ‖(T-B) v‖ := by
  have he : (T-A) v = (T-B) v + (B-A) v := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  have herr : ‖(B-A) v‖ ≤ δ*M := by
    have hnear' : ‖B-A‖ ≤ δ := by simpa only [norm_sub_rev] using hnear
    exact ((B-A).le_opNorm v).trans (mul_le_mul hnear' hv (norm_nonneg v) hδ)
  have hh := norm_add_le ((T-B) v) ((B-A) v)
  rw [← he] at hh
  linarith

theorem norm_operator_partitionWeightedVector_gt [DecidableEq ι]
    (p : ι → C(K, ℝ)) (v : ι → V) (T : V →L[𝕜] W) (U : K → V →L[𝕜] W)
    (f : K → ι → W →L[𝕜] 𝕜) {r η C : ℝ}
    (hC : 0 < C) (hp : ∀ i x, 0 ≤ p i x) (hs : ∀ x, ∑ i, p i x = 1)
    (hdiag : ∀ x i, 0 < p i x → r+η < RCLike.re (f x i ((T-U x) (v i))))
    (hcross : ∀ x i, 0 < p i x →
      ∑ j ∈ Finset.univ.erase i, ‖f x j ((T-U x) (v i))‖ ≤ η)
    (hdual : ∀ x, ‖∑ i, f x i‖ ≤ C) (x : K) :
    r/C < ‖(T-U x) (partitionWeightedVector (𝕜 := 𝕜) p v x)‖ := by
  rw [partitionWeightedVector_apply,map_sum]
  simp_rw [map_smul]
  exact weighted_vector_norm_gt_of_functionals (fun i => p i x)
    (fun i => (T-U x) (v i)) (f x) hC (fun i => hp i x) (hs x)
    (hdiag x) (hcross x) (hdual x)

end ThesisCommon
