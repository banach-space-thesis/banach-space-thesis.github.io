import SurveyStatements.P5Support.LpHaarTraceBalancing

/-! One choice of signs balances finitely many finitely additive traces.
This is the simultaneous selection step for the two-parameter recursion. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem simultaneous_trace_balanced_split {m : ℕ}
    (a : Fin m → LpHaarDyadicSetIndex → 𝕜)
    (hadd : ∀ r i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
      lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j →
        a r k = a r i + a r j)
    {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ r i, ‖a r i‖ ≤
      M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i))
    (n : ℕ) (S : Finset (Fin (2 ^ n))) {ε : ℝ} (hε : 0 < ε)
    (hsmall : (m : ℝ) * (M ^ 2 * intervalLpDyadicRadius n) < (2 * ε) ^ 2) :
    ∃ θ : Fin (2 ^ n) → Bool, ∀ r,
      ‖a r ⟨n + 1, lpHaarSignedChildAtoms n S θ⟩ - (2 : 𝕜)⁻¹ * a r ⟨n, S⟩‖ < ε ∧
      ‖a r ⟨n + 1, lpHaarSignedChildAtoms n S (fun k => !(θ k))⟩ -
        (2 : 𝕜)⁻¹ * a r ⟨n, S⟩‖ < ε := by
  let A (r : Fin m) (k : Fin (2 ^ n)) : 𝕜 :=
    if k ∈ S then a r ⟨n + 1, {lpHaarLeftIndex n k}⟩ else 0
  let B (r : Fin m) (k : Fin (2 ^ n)) : 𝕜 :=
    if k ∈ S then a r ⟨n + 1, {lpHaarRightIndex n k}⟩ else 0
  have hpoint (r : Fin m) (k : Fin (2 ^ n)) :
      ‖A r k - B r k‖ ≤ M * intervalLpDyadicRadius n := by
    by_cases hk : k ∈ S
    · have hl := lpHaarTrace_atom_bound (a r) (ha r) (n + 1) (lpHaarLeftIndex n k)
      have hr := lpHaarTrace_atom_bound (a r) (ha r) (n + 1) (lpHaarRightIndex n k)
      simp only [A, B, if_pos hk]
      have h := norm_sub_le (a r ⟨n + 1, {lpHaarLeftIndex n k}⟩)
        (a r ⟨n + 1, {lpHaarRightIndex n k}⟩)
      rw [lpHaarRadius_succ] at hl hr
      linarith
    · simp only [A, B, if_neg hk, sub_zero, norm_zero]
      exact mul_nonneg hM (intervalLpDyadicRadius_pos n).le
  have htotalnorm (r : Fin m) : (∑ k, ‖A r k - B r k‖) ≤ M := by
    calc
      _ ≤ ∑ _k : Fin (2 ^ n), M * intervalLpDyadicRadius n :=
        Finset.sum_le_sum (fun k _ => hpoint r k)
      _ = ((2 ^ n : ℕ) : ℝ) * (M * intervalLpDyadicRadius n) := by simp
      _ = M * (((2 ^ n : ℕ) : ℝ) * intervalLpDyadicRadius n) := by ring
      _ = M := by rw [lpHaarRadius_cancel, mul_one]
  have hvariance (r : Fin m) :
      (∑ k, ‖A r k - B r k‖ ^ 2) ≤ M ^ 2 * intervalLpDyadicRadius n := by
    calc
      _ ≤ (M * intervalLpDyadicRadius n) * M :=
        haar_sign_variance_le (fun k => A r k - B r k)
          (mul_nonneg hM (intervalLpDyadicRadius_pos n).le) (hpoint r) (htotalnorm r)
      _ = _ := by ring
  have hsum : (∑ r, ∑ k, ‖A r k - B r k‖ ^ 2) < (2 * ε) ^ 2 := by
    calc
      _ ≤ ∑ _r : Fin m, M ^ 2 * intervalLpDyadicRadius n :=
        Finset.sum_le_sum (fun r _ => hvariance r)
      _ = (m : ℝ) * (M ^ 2 * intervalLpDyadicRadius n) := by simp
      _ < _ := hsmall
  obtain ⟨θ, hθ⟩ := haar_trace_sign_balance A B hε hsum
  have hcenter (r : Fin m) : (∑ k : Fin (2 ^ n), (A r k + B r k)) = a r ⟨n, S⟩ := by
    have ht (k : Fin (2 ^ n)) : A r k + B r k = if k ∈ S then a r ⟨n, {k}⟩ else 0 := by
      by_cases hk : k ∈ S
      · simp only [A, B, if_pos hk]
        exact lpHaarDyadicTrace_child_pair (a r) (hadd r) n k (fun _ => true)
      · simp [A, B, hk]
    simp_rw [ht]
    simpa only [Finset.sum_ite_mem, Finset.univ_inter] using
      (lpHaarDyadicTrace_sum_atoms (a r) (hadd r) n S).symm
  have hselected (r : Fin m) (τ : Fin (2 ^ n) → Bool) :
      (∑ k, if τ k then A r k else B r k) = a r ⟨n + 1, lpHaarSignedChildAtoms n S τ⟩ := by
    have ht (k : Fin (2 ^ n)) : (if τ k then A r k else B r k) =
        if k ∈ S then a r ⟨n + 1, {lpHaarSignedChildIndex n τ k}⟩ else 0 := by
      rw [lpHaarSignedChildIndex_choice]
      cases τ k <;> by_cases hk : k ∈ S <;> simp [A, B, hk]
    simp_rw [ht]
    simpa only [Finset.sum_ite_mem, Finset.univ_inter] using
      (lpHaarDyadicTrace_signed_child (a r) (hadd r) n S τ).symm
  have hcomplement (r : Fin m) : (∑ k, if θ k then B r k else A r k) =
      a r ⟨n + 1, lpHaarSignedChildAtoms n S (fun k => !(θ k))⟩ := by
    rw [← hselected r (fun k => !(θ k))]
    apply Finset.sum_congr rfl
    intro k _
    cases θ k <;> rfl
  refine ⟨θ, fun r => ?_⟩
  simpa only [hselected r θ, hcomplement r, hcenter r] using hθ r

end SurveyStatements.P5.BiTree
