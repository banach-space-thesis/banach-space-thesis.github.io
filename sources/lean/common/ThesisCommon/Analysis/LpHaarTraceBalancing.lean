import ThesisCommon.Analysis.LpHaarDyadicTraceAlgebra
import ThesisCommon.Analysis.HaarTraceSignBalancing
import ThesisCommon.Analysis.LpHaarBinarySums

/-! Finite trace balancing inside a prescribed dyadic parent. The
variance is bounded by M^2 times the dyadic mesh, including complex
traces. Refining the parent makes this bound arbitrarily small. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lpHaarTrace_atom_bound (a : LpHaarDyadicSetIndex → 𝕜) {M : ℝ}
    (ha : ∀ i, ‖a i‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i))
    (n : ℕ) (k : Fin (2 ^ n)) : ‖a ⟨n, {k}⟩‖ ≤ M * intervalLpDyadicRadius n := by
  have h := ha ⟨n, {k}⟩
  change ‖a ⟨n, {k}⟩‖ ≤ M *
    (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent n {k}) at h
  rw [lpHaarBlockParent_real_measure] at h
  simpa only [Finset.card_singleton, Nat.cast_one, one_mul] using h

theorem lpHaarSignedChildIndex_choice (n : ℕ) (θ : Fin (2 ^ n) → Bool) (k : Fin (2 ^ n)) :
    lpHaarSignedChildIndex n θ k = if θ k then lpHaarLeftIndex n k else lpHaarRightIndex n k := by
  cases hθ : θ k <;> apply Fin.ext <;>
    simp [lpHaarSignedChildIndex, lpHaarLeftIndex, lpHaarRightIndex, hθ]

theorem lpHaarTrace_balanced_split (a : LpHaarDyadicSetIndex → 𝕜)
    (hadd : ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
      lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j → a k = a i + a j)
    {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, ‖a i‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i))
    (n : ℕ) (S : Finset (Fin (2 ^ n))) {ε : ℝ} (hε : 0 < ε)
    (hsmall : M ^ 2 * intervalLpDyadicRadius n < (2 * ε) ^ 2) :
    ∃ θ : Fin (2 ^ n) → Bool,
      ‖a ⟨n + 1, lpHaarSignedChildAtoms n S θ⟩ - (2 : 𝕜)⁻¹ * a ⟨n, S⟩‖ < ε ∧
      ‖a ⟨n + 1, lpHaarSignedChildAtoms n S (fun k => !(θ k))⟩ -
        (2 : 𝕜)⁻¹ * a ⟨n, S⟩‖ < ε := by
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
  have htotalnorm : (∑ k, ‖A k - B k‖) ≤ M := by
    calc
      _ ≤ ∑ _k : Fin (2 ^ n), M * intervalLpDyadicRadius n := Finset.sum_le_sum (fun k _ => hpoint k)
      _ = ((2 ^ n : ℕ) : ℝ) * (M * intervalLpDyadicRadius n) := by simp
      _ = M * (((2 ^ n : ℕ) : ℝ) * intervalLpDyadicRadius n) := by ring
      _ = M := by rw [lpHaarRadius_cancel, mul_one]
  have hvariance : (∑ k, ‖A k - B k‖ ^ 2) ≤ M ^ 2 * intervalLpDyadicRadius n := by
    calc
      _ ≤ (M * intervalLpDyadicRadius n) * M :=
        haar_sign_variance_le (fun k => A k - B k)
          (mul_nonneg hM (intervalLpDyadicRadius_pos n).le) hpoint htotalnorm
      _ = _ := by ring
  obtain ⟨θ, hθ⟩ := haar_trace_sign_balance (fun _ : Fin 1 => A) (fun _ : Fin 1 => B) hε
    (by simpa only [Fin.sum_univ_one] using hvariance.trans_lt hsmall)
  have hcenter : (∑ k : Fin (2 ^ n), (A k + B k)) = a ⟨n, S⟩ := by
    have ht (k : Fin (2 ^ n)) : A k + B k = if k ∈ S then a ⟨n, {k}⟩ else 0 := by
      by_cases hk : k ∈ S
      · simp only [A, B, if_pos hk]
        exact lpHaarDyadicTrace_child_pair a hadd n k (fun _ => true)
      · simp [A, B, hk]
    simp_rw [ht]
    simpa only [Finset.sum_ite_mem, Finset.univ_inter] using
      (lpHaarDyadicTrace_sum_atoms a hadd n S).symm
  have hselected (τ : Fin (2 ^ n) → Bool) :
      (∑ k, if τ k then A k else B k) = a ⟨n + 1, lpHaarSignedChildAtoms n S τ⟩ := by
    have ht (k : Fin (2 ^ n)) : (if τ k then A k else B k) =
        if k ∈ S then a ⟨n + 1, {lpHaarSignedChildIndex n τ k}⟩ else 0 := by
      rw [lpHaarSignedChildIndex_choice]
      cases τ k <;> by_cases hk : k ∈ S <;> simp [A, B, hk]
    simp_rw [ht]
    simpa only [Finset.sum_ite_mem, Finset.univ_inter] using
      (lpHaarDyadicTrace_signed_child a hadd n S τ).symm
  have hcomplement : (∑ k, if θ k then B k else A k) =
      a ⟨n + 1, lpHaarSignedChildAtoms n S (fun k => !(θ k))⟩ := by
    rw [← hselected (fun k => !(θ k))]
    apply Finset.sum_congr rfl
    intro k _
    cases θ k <;> rfl
  refine ⟨θ, ?_, ?_⟩
  · simpa only [hselected θ, hcenter] using (hθ 0).1
  · simpa only [hcomplement, hcenter] using (hθ 0).2

end ThesisCommon
