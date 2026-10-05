import ThesisCommon.Analysis.CZeroSchauderBasis
import ThesisCommon.Analysis.InfinityScalarRows

/-! Absolute row estimates for genuine scalar functionals on c₀. A nearly
norming positive coordinate leaves uniformly little mass on every other
coordinate. The proof uses finite phase alignment and norm convergence of
finite sections, rather than assuming an ℓ₁ dual representation. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem cZero_functional_row_sum_le (φ : CZeroSum 𝕜 →L[𝕜] 𝕜) (F : Finset ℕ) :
    ∑ n ∈ F, ‖φ (cZeroSingle n 1)‖ ≤ ‖φ‖ := by
  apply (sum_norm_apply_le_of_unit_sums φ (fun n => cZeroSingle n 1) 1 ?_ F).trans_eq
    (mul_one _)
  intro G a ha
  apply (BoundedContinuousFunction.norm_le zero_le_one).2
  intro i
  change ‖(∑ n ∈ G, a n • cZeroSingle n (1 : 𝕜)) i‖ ≤ 1
  rw [cZero_finite_singles_apply]
  split_ifs with hi
  · exact ha i hi
  · simp

theorem cZero_functional_row_summable (φ : CZeroSum 𝕜 →L[𝕜] 𝕜) :
    Summable (fun n => ‖φ (cZeroSingle n 1)‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (cZero_functional_row_sum_le φ)

theorem cZero_functional_norm_eq_tsum (φ : CZeroSum 𝕜 →L[𝕜] 𝕜) :
    ‖φ‖ = ∑' n, ‖φ (cZeroSingle n 1)‖ := by
  have hs := cZero_functional_row_summable φ
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg (fun _ => norm_nonneg _))
    intro x
    apply le_of_tendsto ((φ.continuous.tendsto x).comp
      (cZero_finite_singles_tendsto x)).norm
    apply Eventually.of_forall
    intro N
    change ‖φ (∑ n ∈ Finset.range N, x n • cZeroSingle n (1 : 𝕜))‖ ≤ _
    simp only [map_sum, map_smul]
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖x n‖ * ‖φ (cZeroSingle n 1)‖ := by
        simpa only [norm_smul] using norm_sum_le (Finset.range N)
          (fun n => x n • φ (cZeroSingle n 1))
      _ ≤ ∑ n ∈ Finset.range N, ‖x‖ * ‖φ (cZeroSingle n 1)‖ :=
        Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right
          (BoundedContinuousFunction.norm_coe_le_norm x.toBCF n) (norm_nonneg _))
      _ ≤ ‖x‖ * ∑' n, ‖φ (cZeroSingle n 1)‖ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (hs.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _)) (norm_nonneg x)
      _ = _ := mul_comm _ _
  · exact hs.tsum_le_of_sum_le (cZero_functional_row_sum_le φ)

theorem cZero_functional_near_coordinate (φ : CZeroSum 𝕜 →L[𝕜] 𝕜)
    (n : ℕ) {d δ : ℝ} (hφ : ‖φ‖ ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hdiag : φ (cZeroSingle n 1) = (d : 𝕜)) (hδ : 1 - δ ≤ d) :
    ‖φ - (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n)‖ ≤ 2 * δ := by
  classical
  have hn : ‖φ (cZeroSingle n 1)‖ = d := by
    rw [hdiag, RCLike.norm_ofReal, abs_of_nonneg hd]
  have hr : ‖(φ - (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n)) (cZeroSingle n 1)‖ = 1 - d := by
    simp only [ContinuousLinearMap.sub_apply, cZeroCoordinate_apply, cZeroSingle_apply,
      ite_true, hdiag]
    rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal,
      abs_of_nonpos (sub_nonpos.mpr hd1)]
    ring
  have hrest : (fun i => if i = n then 0 else ‖(φ - (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n)) (cZeroSingle i 1)‖) =
      (fun i => if i = n then 0 else ‖φ (cZeroSingle i 1)‖) := by
    funext i
    split_ifs with hi
    · rfl
    · simp [ContinuousLinearMap.sub_apply, cZeroSingle_apply, Ne.symm hi]
  rw [cZero_functional_norm_eq_tsum,
    (cZero_functional_row_summable (φ - (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n))).tsum_eq_add_tsum_ite n,
    hr, hrest]
  have hsum := cZero_functional_norm_eq_tsum φ
  rw [(cZero_functional_row_summable φ).tsum_eq_add_tsum_ite n, hn] at hsum
  linarith

end ThesisCommon


