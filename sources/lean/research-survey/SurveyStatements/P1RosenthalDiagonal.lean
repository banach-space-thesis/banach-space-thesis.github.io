import SurveyStatements.P1RamseyFusion
import SurveyStatements.P1BasicSequences
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.MetricSpace.Cauchy

/-! Diagonal extraction converts genuine scalar tail diameter estimates
tending to zero into an actual weak-Cauchy subsequence. -/

noncomputable section
set_option autoImplicit false
open Filter Topology Set

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem nestedSubsequences_scalar_diameter_diagonal (s : ℕ → X)
    (ν : ℕ → ℕ → ℕ) (hν : ∀ r, StrictMono (ν r))
    (hnest : ∀ r, range (ν (r + 1)) ⊆ range (ν r))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hdiam : ∀ r (f : X →L[ℂ] ℂ), ∃ N : ℕ,
      ∀ i ≥ N, ∀ j ≥ N, ‖f (s (ν r i)) - f (s (ν r j))‖ ≤ ε r * ‖f‖) :
    ∃ μ : ℕ → ℕ, StrictMono μ ∧ IsWeakCauchySequence (s ∘ μ) := by
  obtain ⟨μ, hμ, htail⟩ := nestedSubsequences_exists_diagonal ν hν hnest
  have hid (n : ℕ) : n ≤ μ n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hμ (Nat.lt_succ_self n)))
  refine ⟨μ, hμ, ?_⟩
  intro f
  apply Metric.cauchySeq_iff.mpr
  intro η hη
  have hl : Tendsto (fun r => ε r * ‖f‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hε.mul_const ‖f‖
  obtain ⟨r, hr⟩ := (hl.eventually (gt_mem_nhds hη)).exists
  obtain ⟨N, hN⟩ := hdiam r f
  let K := max r (ν r N + 1)
  refine ⟨K, ?_⟩
  intro m hm n hn
  have hrm : r ≤ m := (le_max_left _ _).trans hm
  have hrn : r ≤ n := (le_max_left _ _).trans hn
  obtain ⟨i, hi⟩ := htail r m hrm
  obtain ⟨j, hj⟩ := htail r n hrn
  have him : N ≤ i := by
    have hgt : ν r N < μ m := lt_of_lt_of_le (Nat.lt_succ_self _)
      ((le_max_right _ _).trans (hm.trans (hid m)))
    rw [← hi] at hgt
    exact ((hν r).lt_iff_lt.mp hgt).le
  have hjn : N ≤ j := by
    have hgt : ν r N < μ n := lt_of_lt_of_le (Nat.lt_succ_self _)
      ((le_max_right _ _).trans (hn.trans (hid n)))
    rw [← hj] at hgt
    exact ((hν r).lt_iff_lt.mp hgt).le
  have hbound := (hN i him j hjn).trans_lt hr
  simpa only [Function.comp_apply, hi, hj, dist_eq_norm] using hbound

end SurveyStatements.P1
