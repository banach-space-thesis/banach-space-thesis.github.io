import SurveyStatements.P1RosenthalBlocks
import SurveyStatements.P1ScalarClusterPairs

/-! Compactness of the scalar sums of disjoint unit-mass blocks supplies
a unit-mass small block whose scalar coefficient sum is arbitrarily small. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

def coefficientScalarSum (b : ℕ →₀ ℂ) : ℂ :=
  Finsupp.linearCombination ℂ (fun _ : ℕ => (1 : ℂ)) b

theorem coefficientScalarSum_norm_le_mass (b : ℕ →₀ ℂ) :
    ‖coefficientScalarSum b‖ ≤ coefficientL1Mass b := by
  simpa only [coefficientScalarSum, one_mul] using
    bounded_sequence_upper_l1_estimate (fun _ : ℕ => (1 : ℂ))
      (M := 1) (fun _ => by simp) b

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem disjoint_small_blocks_exists_small_scalar_sum (e : ℕ → X)
    (b : ℕ → ℕ →₀ ℂ)
    (hdis : Pairwise (fun i j => Disjoint (b i).support (b j).support))
    (hmass : ∀ n, coefficientL1Mass (b n) = 1) {ε τ : ℝ} (hτ : 0 < τ)
    (hnorm : ∀ n, ‖Finsupp.linearCombination ℂ e (b n)‖ ≤ ε) :
    ∃ c : ℕ →₀ ℂ, coefficientL1Mass c = 1 ∧
      ‖Finsupp.linearCombination ℂ e c‖ ≤ ε ∧ ‖coefficientScalarSum c‖ < τ := by
  classical
  have hin (n : ℕ) : coefficientScalarSum (b n) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hmass] using
      coefficientScalarSum_norm_le_mass (b n)
  obtain ⟨z, hz, ν, hν, hlim⟩ := (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq hin
  have hC := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC (2 * τ) (by positivity)
  have hclose : ‖coefficientScalarSum (b (ν N)) - coefficientScalarSum (b (ν (N + 1)))‖ < 2 * τ := by
    simpa only [Function.comp_apply, dist_eq_norm] using hN N le_rfl (N + 1) (Nat.le_succ N)
  let c : ℕ →₀ ℂ := (1 / 2 : ℂ) • b (ν N) + (-(1 / 2 : ℂ)) • b (ν (N + 1))
  have hh : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  have hbd : Disjoint ((1 / 2 : ℂ) • b (ν N)).support
      ((-(1 / 2 : ℂ)) • b (ν (N + 1))).support :=
    (hdis (ne_of_lt (hν (Nat.lt_succ_self N)))).mono Finsupp.support_smul Finsupp.support_smul
  refine ⟨c, ?_, ?_, ?_⟩
  · dsimp only [c]
    rw [coefficientL1Mass_add_disjoint _ _ hbd, coefficientL1Mass_smul,
      coefficientL1Mass_smul, norm_neg, hh, hmass, hmass]
    norm_num
  · dsimp only [c]
    rw [map_add, map_smul, map_smul]
    calc
      _ ≤ ‖(1 / 2 : ℂ) • Finsupp.linearCombination ℂ e (b (ν N))‖ +
          ‖(-(1 / 2 : ℂ)) • Finsupp.linearCombination ℂ e (b (ν (N + 1)))‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖Finsupp.linearCombination ℂ e (b (ν N))‖ +
          (1 / 2 : ℝ) * ‖Finsupp.linearCombination ℂ e (b (ν (N + 1)))‖ := by
        simp only [norm_smul, norm_neg, hh]
      _ ≤ ε := by linarith [hnorm (ν N), hnorm (ν (N + 1))]
  · have heq : coefficientScalarSum c = (1 / 2 : ℂ) *
        (coefficientScalarSum (b (ν N)) - coefficientScalarSum (b (ν (N + 1)))) := by
      simp only [coefficientScalarSum, c, map_add, map_smul, smul_eq_mul]
      ring
    rw [heq, norm_mul, hh]
    linarith

end SurveyStatements.P1
