import Mathlib.Order.Interval.Finset.Nat

/-! Increasing enumeration and diagonal fusion on genuine infinite subsets
of the natural numbers, for the elementary Ramsey proof of the complex
Rosenthal dichotomy. -/

noncomputable section
set_option autoImplicit false
open Set

namespace SurveyStatements.P1

theorem infiniteSet_exists_strictMono_sequence (M : Set ℕ) (hM : M.Infinite) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∀ n, ν n ∈ M := by
  apply Nat.exists_strictMono_subsequence
  intro N
  obtain ⟨n, hn, hNn⟩ := hM.exists_gt N
  exact ⟨n, hNn, hn⟩

theorem infiniteSet_inter_Ioi (M : Set ℕ) (hM : M.Infinite) (a : ℕ) :
    (M ∩ Ioi a).Infinite := by
  apply (hM.diff (Set.finite_Iic a)).mono
  intro n hn
  exact ⟨hn.1, show a < n from lt_of_not_ge hn.2⟩

theorem nestedInfiniteSets_exists_diagonal (M : ℕ → Set ℕ)
    (hInf : ∀ n, (M n).Infinite) (hNest : ∀ n, M (n + 1) ⊆ M n) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∀ n k, n ≤ k → ν k ∈ M n := by
  classical
  choose next hmem hgt using fun n N => (hInf n).exists_gt N
  let ν : ℕ → ℕ := Nat.rec (next 0 0) (fun n i => next (n + 1) i)
  have hνnext (n : ℕ) : ν (n + 1) = next (n + 1) (ν n) := rfl
  have hν : StrictMono ν := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hνnext]
    exact hgt (n + 1) (ν n)
  have hνmem (n : ℕ) : ν n ∈ M n := by
    cases n with
    | zero => exact hmem 0 0
    | succ n => exact hmem (n + 1) (ν n)
  have hanti : Antitone M := antitone_nat_of_succ_le hNest
  exact ⟨ν, hν, fun n k hnk => hanti hnk (hνmem k)⟩

theorem nestedSubsequences_exists_diagonal (ν : ℕ → ℕ → ℕ)
    (hν : ∀ n, StrictMono (ν n))
    (hNest : ∀ n, range (ν (n + 1)) ⊆ range (ν n)) :
    ∃ μ : ℕ → ℕ, StrictMono μ ∧
      ∀ n k, n ≤ k → μ k ∈ range (ν n) := by
  apply nestedInfiniteSets_exists_diagonal (fun n => range (ν n))
  · exact fun n => Set.infinite_range_of_injective (hν n).injective
  · exact hNest

end SurveyStatements.P1
