import SurveyStatements.P1ConstantSuppression
import Mathlib.Data.Nat.Lattice

/-! Initial projections control finite coefficient tails. Cutting before a
chosen witness point multiplies the norm by at most three and retains the
constant-modulus coefficient property. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem finite_unitModulus_linearCombination_norm_lower (e : ℕ → X)
    (he : ∀ n, ‖e n‖ = 1)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (a : ℕ →₀ ℂ) (ha : ∀ i ∈ a.support, ‖a i‖ = 1) (hne : a.support.Nonempty) :
    (1 / 4 : ℝ) ≤ ‖Finsupp.linearCombination ℂ e a‖ := by
  obtain ⟨i, hi⟩ := hne
  have h := uniform_partialSum_finsupp_coefficient_bound he (by norm_num) hp a i
  rw [ha i hi] at h
  linarith

theorem finite_prefix_linearCombination (e : ℕ → X) (a : ℕ →₀ ℂ) (N : ℕ) :
    Finsupp.linearCombination ℂ e (a.filter (fun i => i < N)) = sequencePartialSum e a N := by
  have hs : (a.filter (fun i => i < N)).support ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  rw [linearCombination_eq_partialSum e _ hs]
  unfold sequencePartialSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finsupp.filter_apply_pos (fun j => j < N) a (Finset.mem_range.mp hi)]

theorem finite_coefficient_prefix_tail_split (a : ℕ →₀ ℂ) (N : ℕ) :
    a.filter (fun i => i < N) + a.filter (fun i => N ≤ i) = a := by
  ext i
  by_cases hi : i < N
  · simp [Finsupp.filter_apply, hi, Nat.not_le_of_gt hi]
  · simp [Finsupp.filter_apply, hi, Nat.le_of_not_gt hi]

theorem finite_coefficient_tail_norm_bound (e : ℕ → X)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (a : ℕ →₀ ℂ) (N : ℕ) :
    ‖Finsupp.linearCombination ℂ e (a.filter (fun i => N ≤ i))‖ ≤
      3 * ‖Finsupp.linearCombination ℂ e a‖ := by
  obtain ⟨M, hM⟩ := a.support.exists_nat_subset_range
  have hs : a.support ⊆ Finset.range (max N M) := hM.trans
    (Finset.range_mono (Nat.le_max_right _ _))
  have hprefix := hp N (max N M) (Nat.le_max_left _ _) a
  rw [← linearCombination_eq_partialSum e a hs] at hprefix
  have hsum : sequencePartialSum e a N +
      Finsupp.linearCombination ℂ e (a.filter (fun i => N ≤ i)) =
      Finsupp.linearCombination ℂ e a := by
    rw [← finite_prefix_linearCombination e a N, ← map_add,
      finite_coefficient_prefix_tail_split]
  have htail : Finsupp.linearCombination ℂ e (a.filter (fun i => N ≤ i)) =
      Finsupp.linearCombination ℂ e a - sequencePartialSum e a N :=
    (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hsum)
  rw [htail]
  have hnorm := norm_sub_le (Finsupp.linearCombination ℂ e a) (sequencePartialSum e a N)
  linarith

theorem finite_coefficient_tail_preserves_unitModulus (a : ℕ →₀ ℂ)
    (ha : ∀ i ∈ a.support, ‖a i‖ = 1) (N : ℕ) :
    ∀ i ∈ (a.filter (fun i => N ≤ i)).support,
      ‖a.filter (fun i => N ≤ i) i‖ = 1 := by
  intro i hi
  obtain ⟨hi, hNi⟩ := Finset.mem_filter.mp hi
  rw [Finsupp.filter_apply_pos (fun j => N ≤ j) a hNi]
  exact ha i hi

theorem finite_coefficient_tail_first_support (a : ℕ →₀ ℂ) (S : Finset ℕ)
    (hS : S.Nonempty) (hsupp : S ⊆ a.support) :
    sInf ((a.filter (fun i => sInf (S : Set ℕ) ≤ i)).support : Set ℕ) =
      sInf (S : Set ℕ) := by
  let k := sInf (S : Set ℕ)
  have hkS : k ∈ S := Nat.sInf_mem (Finset.coe_nonempty.mpr hS)
  have hk : k ∈ (a.filter (fun i => k ≤ i)).support :=
    Finset.mem_filter.mpr ⟨hsupp hkS, le_rfl⟩
  apply le_antisymm (Nat.sInf_le (show k ∈
    (((a.filter (fun i => k ≤ i)).support : Finset ℕ) : Set ℕ) from hk))
  have hnonempty : (((a.filter (fun i => k ≤ i)).support : Finset ℕ) : Set ℕ).Nonempty := ⟨k, hk⟩
  exact (Finset.mem_filter.mp (Nat.sInf_mem hnonempty)).2

end SurveyStatements.P1
