import SurveyStatements.P1WeakCauchyBidual
import Mathlib.Tactic.Abel

/-! Ordered summation by parts for the difference sequence. These exact
finite identities are the scalar-series/coefficient-convergence connection
in Rosenthal's Proposition 2.3. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def sequenceDifference (b : ℕ → X) : ℕ → X
  | 0 => b 0
  | n + 1 => b (n + 1) - b n

theorem sequencePartialSum_succ (e : ℕ → X) (a : ℕ → ℂ) (N : ℕ) :
    sequencePartialSum e a (N + 1) = sequencePartialSum e a N + a N • e N := by
  simp only [sequencePartialSum, Finset.sum_range_succ]

theorem difference_partialSum_succ (b : ℕ → X) (c : ℕ → ℂ) (N : ℕ) :
    sequencePartialSum (sequenceDifference b) c (N + 1) =
      sequencePartialSum b (fun n => c n - c (n + 1)) N + c N • b N := by
  induction N with
  | zero => simp [sequencePartialSum, sequenceDifference]
  | succ N ih =>
    rw [sequencePartialSum_succ (sequenceDifference b) c (N + 1), ih,
      sequencePartialSum_succ b (fun n => c n - c (n + 1)) N]
    simp only [sequenceDifference, smul_sub, sub_smul]
    abel

theorem difference_prefix_ones (b : ℕ → X) (N : ℕ) :
    sequencePartialSum (sequenceDifference b) (fun _ => 1) (N + 1) = b N := by
  rw [difference_partialSum_succ]
  simp [sequencePartialSum]

theorem scalar_difference_partialSum (c : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (c n - c (n + 1))) = c 0 - c N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    abel

theorem weakCauchy_difference_prefixes (b : ℕ → X)
    (hb : IsWeakCauchySequence b) :
    IsWeakCauchySequence (fun N =>
      sequencePartialSum (sequenceDifference b) (fun _ => 1) (N + 1)) := by
  simpa only [difference_prefix_ones] using hb

theorem stronglySumming_difference_coefficients_converge
    (b : ℕ → X) (hb : IsStronglySumming b) {M : ℝ}
    (hM : ∀ n, ‖b n‖ ≤ M) (c : ℕ → ℂ)
    (hc : HasBoundedPartialSums (sequenceDifference b) c)
    (hcBounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ n, ‖c n‖ ≤ R) :
    ∃ z : ℂ, Tendsto c atTop (𝓝 z) := by
  obtain ⟨C, hC⟩ := hc
  obtain ⟨R, hR, hcR⟩ := hcBounded
  have hbounded : HasBoundedPartialSums b (fun n => c n - c (n + 1)) := by
    refine ⟨C + R * M, ?_⟩
    intro N
    have hiden : sequencePartialSum b (fun n => c n - c (n + 1)) N =
        sequencePartialSum (sequenceDifference b) c (N + 1) - c N • b N := by
      rw [difference_partialSum_succ]
      simp only [add_sub_cancel_right]
    rw [hiden]
    calc
      _ ≤ ‖sequencePartialSum (sequenceDifference b) c (N + 1)‖ + ‖c N • b N‖ :=
        norm_sub_le _ _
      _ ≤ C + R * M := by
        apply add_le_add (hC _)
        rw [norm_smul]
        exact mul_le_mul (hcR N) (hM N) (norm_nonneg _) hR
  obtain ⟨z, hz⟩ := hb.2.2 (fun n => c n - c (n + 1)) hbounded
  refine ⟨c 0 - z, ?_⟩
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c 0) atTop (𝓝 (c 0))).sub hz
  simpa only [scalar_difference_partialSum, sub_sub_cancel] using ht

theorem difference_coefficient_convergence_implies_stronglySumming
    (b : ℕ → X) (hb : IsBasicSequence b) (hweak : IsWeakCauchySequence b)
    {M D : ℝ} (hM : ∀ n, ‖b n‖ ≤ M) (hD : 0 ≤ D)
    (hdom : ∀ a : ℕ → ℂ, ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, a n‖ ≤ D * ‖sequencePartialSum b a N‖)
    (hcc : ∀ c : ℕ → ℂ, HasBoundedPartialSums (sequenceDifference b) c →
      ∃ z : ℂ, Tendsto c atTop (𝓝 z)) :
    IsStronglySumming b := by
  refine ⟨hb, hweak, ?_⟩
  intro a ha
  obtain ⟨C, hC⟩ := ha
  have hCnonneg : 0 ≤ C := by simpa [sequencePartialSum] using hC 0
  let c : ℕ → ℂ := fun N => -(∑ n ∈ Finset.range N, a n)
  have hcDiff (n : ℕ) : c n - c (n + 1) = a n := by
    dsimp [c]
    rw [Finset.sum_range_succ]
    abel
  have hcNorm (n : ℕ) : ‖c n‖ ≤ D * C := by
    have h : ‖c n‖ ≤ D * ‖sequencePartialSum b a n‖ := by
      simpa [c] using hdom a n
    exact h.trans
      (mul_le_mul_of_nonneg_left (hC n) hD)
  have hpartial : HasBoundedPartialSums (sequenceDifference b) c := by
    refine ⟨C + (D * C) * M, ?_⟩
    intro N
    cases N with
    | zero =>
      simp only [sequencePartialSum, Finset.range_zero, Finset.sum_empty, norm_zero]
      have hMnonneg : 0 ≤ M := (norm_nonneg (b 0)).trans (hM 0)
      positivity
    | succ N =>
      rw [difference_partialSum_succ]
      simp only [hcDiff]
      calc
        _ ≤ ‖sequencePartialSum b a N‖ + ‖c N • b N‖ := norm_add_le _ _
        _ ≤ C + (D * C) * M := by
          apply add_le_add (hC N)
          rw [norm_smul]
          exact mul_le_mul (hcNorm N) (hM N) (norm_nonneg _) (mul_nonneg hD hCnonneg)
  obtain ⟨z, hz⟩ := hcc c hpartial
  refine ⟨-z, ?_⟩
  simpa only [c, neg_neg] using hz.neg

end SurveyStatements.P1
