import SurveyStatements.P1WeakNullSelectionStep
import Mathlib.Order.Monotone.Basic

/-! Recursive subsequence selection with prescribed one-step projection
losses. The selected vectors remain terms of the original weakly-null sequence. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

private theorem weakNull_state_exists (y : ℕ → X) (hynorm : ∀ n, ‖y n‖ = 1)
    (hy : ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (s : Finset X × ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ n : ℕ, s.2 ≤ n ∧ ∀ x ∈ Submodule.span ℂ (s.1 : Set X), ∀ a : ℂ,
      c * ‖x‖ ≤ ‖x + a • y n‖ := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (s.1 : Set X)) :=
    FiniteDimensional.span_of_finite ℂ s.1.finite_toSet
  exact weakNull_finite_selection_step y hynorm hy _ hc0 hc1 s.2

private def weakNull_selectionIndex (y : ℕ → X) (hynorm : ∀ n, ‖y n‖ = 1)
    (hy : ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (s : Finset X × ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : ℕ :=
  Classical.choose (weakNull_state_exists y hynorm hy s hc0 hc1)

private def weakNull_selectionNext (y : ℕ → X) (hynorm : ∀ n, ‖y n‖ = 1)
    (hy : ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (s : Finset X × ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : Finset X × ℕ := by
  classical
  let n := weakNull_selectionIndex y hynorm hy s hc0 hc1
  exact (insert (y n) s.1, n + 1)

private def weakNull_selectionStates (y : ℕ → X) (hynorm : ∀ n, ‖y n‖ = 1)
    (hy : ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 < c n) (hc1 : ∀ n, c n < 1) : ℕ → Finset X × ℕ
  | 0 => (∅, 0)
  | n + 1 => weakNull_selectionNext y hynorm hy
      (weakNull_selectionStates y hynorm hy c hc0 hc1 n) (hc0 n) (hc1 n)

theorem exists_weakNull_oneStep_subsequence (y : ℕ → X) (hynorm : ∀ n, ‖y n‖ = 1)
    (hy : ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 < c n) (hc1 : ∀ n, c n < 1) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ n : ℕ, ∀ a : ℕ → ℂ,
        c n * ‖sequencePartialSum (y ∘ ν) a n‖ ≤
          ‖sequencePartialSum (y ∘ ν) a (n + 1)‖ := by
  classical
  let s := weakNull_selectionStates y hynorm hy c hc0 hc1
  let ν : ℕ → ℕ := fun n => weakNull_selectionIndex y hynorm hy (s n) (hc0 n) (hc1 n)
  let e : ℕ → X := y ∘ ν
  have hspec (n : ℕ) : (s n).2 ≤ ν n ∧
      ∀ x ∈ Submodule.span ℂ ((s n).1 : Set X), ∀ a : ℂ,
        c n * ‖x‖ ≤ ‖x + a • e n‖ :=
    Classical.choose_spec (weakNull_state_exists y hynorm hy (s n) (hc0 n) (hc1 n))
  have hnext (n : ℕ) : s (n + 1) = (insert (e n) (s n).1, ν n + 1) := rfl
  have hν : StrictMono ν := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hn := (hspec (n + 1)).1
    rw [hnext] at hn
    exact Nat.lt_of_succ_le hn
  have hmono : Monotone (fun n => (s n).1) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hnext]
    exact Finset.subset_insert _ _
  have hprev {i n : ℕ} (hin : i < n) : e i ∈ (s n).1 := by
    apply hmono (Nat.succ_le_of_lt hin)
    change e i ∈ (s (i + 1)).1
    rw [hnext]
    exact Finset.mem_insert_self _ _
  refine ⟨ν, hν, ?_⟩
  intro n a
  have hp : sequencePartialSum e a n ∈ Submodule.span ℂ ((s n).1 : Set X) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hprev (Finset.mem_range.mp hi)))
  simpa only [sequencePartialSum, Finset.sum_range_succ] using
    (hspec n).2 (sequencePartialSum e a n) hp (a n)

end SurveyStatements.P1
