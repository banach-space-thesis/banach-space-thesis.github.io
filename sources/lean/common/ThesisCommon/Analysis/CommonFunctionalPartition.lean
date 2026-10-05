import ThesisCommon.Analysis.FinitePartitionBadVectors

/-! Detection of a continuous positive vector combination by one genuine
bounded functional, with explicit stability under a nearby operator. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 E F K ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace K]

theorem common_functional_weighted_norm_gt
    (w : ι → ℝ) (v : ι → F) (φ : F →L[𝕜] 𝕜) {r C : ℝ}
    (hC : 0 < C) (hφ : ‖φ‖ ≤ C) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hdet : ∀ i, 0 < w i → r < RCLike.re (φ (v i))) :
    r/C < ‖∑ i, (w i : 𝕜) • v i‖ := by
  have he : RCLike.re (φ (∑ i, (w i : 𝕜) • v i)) =
      ∑ i, w i * RCLike.re (φ (v i)) := by
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,smul_eq_mul,RCLike.re_ofReal_mul]
  have hlo : r < RCLike.re (φ (∑ i, (w i : 𝕜) • v i)) := by
    rw [he]
    exact strict_lower_bound_positive_weighted_sum w _ hw hs hdet
  have hup := (RCLike.re_le_norm (φ (∑ i, (w i : 𝕜) • v i))).trans
    ((φ.le_opNorm _).trans (mul_le_mul_of_nonneg_right hφ (norm_nonneg _)))
  exact (div_lt_iff₀ hC).mpr (by nlinarith)

theorem re_operator_apply_gt_of_near
    (φ : F →L[𝕜] 𝕜) (T A B : E →L[𝕜] F) (v : E) {r C δ M : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hφ : ‖φ‖ ≤ C) (hv : ‖v‖ ≤ M)
    (hnear : ‖A-B‖ ≤ δ)
    (hbad : r+C*δ*M < RCLike.re (φ ((T-A) v))) :
    r < RCLike.re (φ ((T-B) v)) := by
  have he : φ ((T-A) v)-φ ((T-B) v) = φ ((B-A) v) := by
    rw [← map_sub]
    congr 1
    simp only [ContinuousLinearMap.sub_apply]
    abel
  have herr : ‖φ ((B-A) v)‖ ≤ C*δ*M := by
    have hnear' : ‖B-A‖ ≤ δ := by simpa only [norm_sub_rev] using hnear
    calc
      _ ≤ C*‖(B-A) v‖ := (φ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hφ (norm_nonneg _))
      _ ≤ C*(δ*M) := mul_le_mul_of_nonneg_left
        (((B-A).le_opNorm v).trans (mul_le_mul hnear' hv (norm_nonneg _) hδ)) hC
      _ = _ := by ring
  have hre := RCLike.re_le_norm (φ ((T-A) v)-φ ((T-B) v))
  rw [map_sub,he] at hre
  linarith

theorem norm_partition_operator_gt_of_common_functional
    (p : ι → C(K,ℝ)) (v : ι → E) (T : E →L[𝕜] F)
    (A : ι → E →L[𝕜] F) (U : K → E →L[𝕜] F) (φ : F →L[𝕜] 𝕜)
    {r C δ M : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hφ : ‖φ‖ ≤ C)
    (hp : ∀ i x, 0 ≤ p i x) (hs : ∀ x, ∑ i, p i x = 1)
    (hv : ∀ i, ‖v i‖ ≤ M)
    (hnear : ∀ x i, 0 < p i x → ‖A i-U x‖ ≤ δ)
    (hbad : ∀ i, r+C*δ*M < RCLike.re (φ ((T-A i) (v i)))) (x : K) :
    r/C < ‖(T-U x) (partitionWeightedVector (𝕜 := 𝕜) p v x)‖ := by
  rw [partitionWeightedVector_apply,map_sum]
  simp_rw [map_smul]
  exact common_functional_weighted_norm_gt (fun i => p i x) _ φ hC hφ
    (fun i => hp i x) (hs x) (fun i hi =>
      re_operator_apply_gt_of_near φ T (A i) (U x) (v i) hC.le hδ hφ
        (hv i) (hnear x i hi) (hbad i))

end ThesisCommon
