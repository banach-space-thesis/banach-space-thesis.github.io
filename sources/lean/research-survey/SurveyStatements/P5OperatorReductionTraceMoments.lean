import SurveyStatements.P5Support.LpHaarTraceBalancing
import SurveyStatements.P5OperatorReductionMoments

/-! Actual dyadic trace balancing errors have small finite second
moments. This permits their simultaneous selection with the linear and
quadratic operator errors using one common sign cube. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lpHaarTrace_split_second_moment_le (a : LpHaarDyadicSetIndex → 𝕜)
    (hadd : ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
      lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j → a k = a i + a j)
    {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, ‖a i‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i))
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖a ⟨n + 1, lpHaarSignedChildAtoms n S θ⟩ -
        (2 : 𝕜)⁻¹ * a ⟨n, S⟩‖ ^ 2) ≤
          M ^ 2 * intervalLpDyadicRadius n / 4 := by
  let A (k : Fin (2 ^ n)) : 𝕜 := if k ∈ S then a ⟨n + 1, {lpHaarLeftIndex n k}⟩ else 0
  let B (k : Fin (2 ^ n)) : 𝕜 := if k ∈ S then a ⟨n + 1, {lpHaarRightIndex n k}⟩ else 0
  have hpoint (k : Fin (2 ^ n)) : ‖A k - B k‖ ≤ M * intervalLpDyadicRadius n := by
    by_cases hk : k ∈ S
    · have hl := lpHaarTrace_atom_bound a ha (n + 1) (lpHaarLeftIndex n k)
      have hr := lpHaarTrace_atom_bound a ha (n + 1) (lpHaarRightIndex n k)
      simp only [A, B, if_pos hk]
      have h := norm_sub_le (a ⟨n + 1, {lpHaarLeftIndex n k}⟩)
        (a ⟨n + 1, {lpHaarRightIndex n k}⟩)
      rw [lpHaarRadius_succ] at hl hr
      linarith
    · simp only [A, B, if_neg hk, sub_zero, norm_zero]
      exact mul_nonneg hM (intervalLpDyadicRadius_pos n).le
  have htotal : (∑ k, ‖A k - B k‖) ≤ M := by
    calc
      _ ≤ ∑ _k : Fin (2 ^ n), M * intervalLpDyadicRadius n :=
        Finset.sum_le_sum (fun k _ => hpoint k)
      _ = ((2 ^ n : ℕ) : ℝ) * (M * intervalLpDyadicRadius n) := by simp
      _ = M * (((2 ^ n : ℕ) : ℝ) * intervalLpDyadicRadius n) := by ring
      _ = M := by rw [lpHaarRadius_cancel, mul_one]
  have hvariance : (∑ k, ‖A k - B k‖ ^ 2) ≤ M ^ 2 * intervalLpDyadicRadius n := by
    calc
      _ ≤ (M * intervalLpDyadicRadius n) * M :=
        haar_sign_variance_le (fun k => A k - B k)
          (mul_nonneg hM (intervalLpDyadicRadius_pos n).le) hpoint htotal
      _ = _ := by ring
  have hcenter : (∑ k : Fin (2 ^ n), (A k + B k)) = a ⟨n, S⟩ := by
    have ht (k : Fin (2 ^ n)) : A k + B k = if k ∈ S then a ⟨n, {k}⟩ else 0 := by
      by_cases hk : k ∈ S
      · simp only [A, B, if_pos hk]
        exact lpHaarDyadicTrace_child_pair a hadd n k (fun _ => true)
      · simp [A, B, hk]
    simp_rw [ht]
    simpa only [Finset.sum_ite_mem, Finset.univ_inter] using
      (lpHaarDyadicTrace_sum_atoms a hadd n S).symm
  have hselected (θ : Fin (2 ^ n) → Bool) :
      (∑ k, if θ k then A k else B k) = a ⟨n + 1, lpHaarSignedChildAtoms n S θ⟩ := by
    have ht (k : Fin (2 ^ n)) : (if θ k then A k else B k) =
        if k ∈ S then a ⟨n + 1, {lpHaarSignedChildIndex n θ k}⟩ else 0 := by
      rw [lpHaarSignedChildIndex_choice]
      cases θ k <;> by_cases hk : k ∈ S <;> simp [A, B, hk]
    simp_rw [ht]
    simpa only [Finset.sum_ite_mem, Finset.univ_inter] using
      (lpHaarDyadicTrace_signed_child a hadd n S θ).symm
  have heq (θ : Fin (2 ^ n) → Bool) :
      a ⟨n + 1, lpHaarSignedChildAtoms n S θ⟩ - (2 : 𝕜)⁻¹ * a ⟨n, S⟩ =
        (2 : 𝕜)⁻¹ * ∑ k, signedValue (θ k) (A k - B k) := by
    simpa only [hselected θ, hcenter] using haar_trace_signed_deviation A B θ
  simp_rw [heq, norm_mul, mul_pow]
  rw [mean_mul_left, haar_sign_second_moment]
  have htwo : ‖(2 : 𝕜)⁻¹‖ ^ 2 = (1 / 4 : ℝ) := by
    rw [norm_inv]
    norm_num
  rw [htwo]
  nlinarith

end SurveyStatements.P5OperatorReduction
