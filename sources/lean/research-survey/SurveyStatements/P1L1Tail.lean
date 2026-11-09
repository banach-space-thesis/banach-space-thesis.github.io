import SurveyStatements.P1BasicCriterion
import SurveyStatements.P1Transfer
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Finite ℓ₁ coefficient norms and stabilized tail lower norms. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

def coefficientL1Mass (b : ℕ →₀ ℂ) : ℝ := b.sum (fun _ z => ‖z‖)

theorem coefficientL1Mass_nonneg (b : ℕ →₀ ℂ) : 0 ≤ coefficientL1Mass b := by
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

@[simp] theorem coefficientL1Mass_single (i : ℕ) (z : ℂ) :
    coefficientL1Mass (Finsupp.single i z) = ‖z‖ := by
  simp [coefficientL1Mass]

theorem coefficientL1Mass_smul (z : ℂ) (b : ℕ →₀ ℂ) :
    coefficientL1Mass (z • b) = ‖z‖ * coefficientL1Mass b := by
  rw [coefficientL1Mass, Finsupp.sum_smul_index' (fun _ => norm_zero)]
  simp only [norm_smul, Finsupp.sum, coefficientL1Mass, Finset.mul_sum]

theorem coefficientL1Mass_add_disjoint (a b : ℕ →₀ ℂ)
    (hdisjoint : Disjoint a.support b.support) :
    coefficientL1Mass (a + b) = coefficientL1Mass a + coefficientL1Mass b := by
  classical
  unfold coefficientL1Mass
  rw [Finsupp.sum_of_support_subset (a + b) Finsupp.support_add
    (fun _ z => ‖z‖) (fun _ _ => norm_zero),
    Finsupp.sum_of_support_subset a Finset.subset_union_left
    (fun _ z => ‖z‖) (fun _ _ => norm_zero),
    Finsupp.sum_of_support_subset b Finset.subset_union_right
    (fun _ z => ‖z‖) (fun _ _ => norm_zero), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hai : i ∈ a.support
  · have hbi : i ∉ b.support := fun hbi => Finset.disjoint_left.mp hdisjoint hai hbi
    simp [Finsupp.notMem_support_iff.mp hbi]
  · simp [Finsupp.notMem_support_iff.mp hai]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def l1TailNorms (e : ℕ → X) (N : ℕ) : Set ℝ :=
  {t | ∃ b : ℕ →₀ ℂ, (∀ i ∈ b.support, N ≤ i) ∧
    coefficientL1Mass b = 1 ∧ t = ‖Finsupp.linearCombination ℂ e b‖}

def l1TailLowerNorm (e : ℕ → X) (N : ℕ) : ℝ := sInf (l1TailNorms e N)

theorem l1TailNorms_nonempty (e : ℕ → X) (N : ℕ) : (l1TailNorms e N).Nonempty := by
  refine ⟨‖e N‖, Finsupp.single N 1, ?_, by simp, by simp⟩
  intro i hi
  have hiN : i = N := by
    simpa only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] using hi
  omega

theorem l1TailNorms_bddBelow (e : ℕ → X) (N : ℕ) : BddBelow (l1TailNorms e N) := by
  refine ⟨0, ?_⟩
  rintro t ⟨b, _, _, rfl⟩
  exact norm_nonneg _

theorem l1TailLowerNorm_le (e : ℕ → X) (N : ℕ) (b : ℕ →₀ ℂ)
    (hsupp : ∀ i ∈ b.support, N ≤ i) (hmass : coefficientL1Mass b = 1) :
    l1TailLowerNorm e N ≤ ‖Finsupp.linearCombination ℂ e b‖ :=
  csInf_le (l1TailNorms_bddBelow e N) ⟨b, hsupp, hmass, rfl⟩

theorem l1TailLowerNorm_bounds (e : ℕ → X) {L U : ℝ}
    (hlower : ∀ b : ℕ →₀ ℂ, L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ e b‖)
    (hupper : ∀ b : ℕ →₀ ℂ, ‖Finsupp.linearCombination ℂ e b‖ ≤ U * coefficientL1Mass b)
    (N : ℕ) : L ≤ l1TailLowerNorm e N ∧ l1TailLowerNorm e N ≤ U := by
  constructor
  · apply le_csInf (l1TailNorms_nonempty e N)
    rintro t ⟨b, _, hb, rfl⟩
    simpa [hb] using hlower b
  · have hsingle : l1TailLowerNorm e N ≤ ‖e N‖ := by
      have hsupp : ∀ i ∈ (Finsupp.single N (1 : ℂ)).support, N ≤ i := by
        intro i hi
        have hiN : i = N := by
          simpa only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] using hi
        omega
      simpa using l1TailLowerNorm_le e N (Finsupp.single N 1) hsupp (by simp)
    exact hsingle.trans (by simpa using hupper (Finsupp.single N 1))

theorem l1TailLowerNorm_monotone (e : ℕ → X) : Monotone (l1TailLowerNorm e) := by
  intro N M hNM
  apply csInf_le_csInf (l1TailNorms_bddBelow e N) (l1TailNorms_nonempty e M)
  rintro t ⟨b, hb, hmass, rfl⟩
  exact ⟨b, fun i hi => hNM.trans (hb i hi), hmass, rfl⟩

/-- A positive lower ℓ₁ estimate gives a positive stabilized tail lower norm.
Every tail has finite unit-mass blocks within one tenth of this norm. -/
theorem l1TailLowerNorm_stabilizes (e : ℕ → X) {L U : ℝ} (hL : 0 < L)
    (hlower : ∀ b : ℕ →₀ ℂ, L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ e b‖)
    (hupper : ∀ b : ℕ →₀ ℂ, ‖Finsupp.linearCombination ℂ e b‖ ≤ U * coefficientL1Mass b) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ,
      (9 / 10 : ℝ) * A < l1TailLowerNorm e N ∧
      ∀ M : ℕ, ∃ b : ℕ →₀ ℂ, (∀ i ∈ b.support, M ≤ i) ∧
        coefficientL1Mass b = 1 ∧ ‖Finsupp.linearCombination ℂ e b‖ < (11 / 10 : ℝ) * A := by
  let A : ℝ := sSup (Set.range (l1TailLowerNorm e))
  have hB : BddAbove (Set.range (l1TailLowerNorm e)) := by
    refine ⟨U, ?_⟩
    rintro t ⟨n, rfl⟩
    exact (l1TailLowerNorm_bounds e hlower hupper n).2
  have hle (n : ℕ) : l1TailLowerNorm e n ≤ A := le_csSup hB ⟨n, rfl⟩
  have hA : 0 < A := hL.trans_le ((l1TailLowerNorm_bounds e hlower hupper 0).1.trans (hle 0))
  obtain ⟨t, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (Set.range_nonempty (l1TailLowerNorm e))
    (show (9 / 10 : ℝ) * A < A by linarith)
  refine ⟨A, hA, N, hN, ?_⟩
  intro M
  obtain ⟨t, ⟨b, hsupp, hmass, rfl⟩, hb⟩ := exists_lt_of_csInf_lt (l1TailNorms_nonempty e M)
    (show l1TailLowerNorm e M < (11 / 10 : ℝ) * A from
      (hle M).trans_lt (by linarith))
  exact ⟨b, hsupp, hmass, hb⟩

end SurveyStatements.P1
