import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! Finite-test separation. In Sigma Section 4 the tests are Boolean-algebra sets
and `ev μ A` is the finitely additive measure μ evaluated on A. The result below
applies to these measures without assuming countable additivity.
-/
noncomputable section
namespace ThesisCommon
open scoped BigOperators
variable {D I : Type*}

/-- Uniform separation by finitely many admissible real-valued tests. -/
def FinitelySeparated (ev : D → I → ℝ) (S : Set I) (M N : Set D) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ F : Finset I, (↑F : Set I) ⊆ S ∧
    ∀ m ∈ M, ∀ n ∈ N, ∃ i ∈ F, ε ≤ |ev m i - ev n i|

theorem finitelySeparated_symm {ev : D → I → ℝ} {S : Set I} {M N : Set D}
    (h : FinitelySeparated ev S M N) : FinitelySeparated ev S N M := by
  rcases h with ⟨ε, hε, F, hF, h⟩
  refine ⟨ε, hε, F, hF, ?_⟩
  intro n hn m hm
  simpa only [abs_sub_comm] using h m hm n hn

theorem finitelySeparated_mono_tests {ev : D → I → ℝ} {S T : Set I} {M N : Set D}
    (hST : S ⊆ T) (h : FinitelySeparated ev S M N) : FinitelySeparated ev T M N := by
  rcases h with ⟨ε, hε, F, hF, h⟩
  exact ⟨ε, hε, F, hF.trans hST, h⟩

/-- The finite-sum estimate behind Sigma Lemma 4.2. A positive gap in a simple
function's integrals yields a positive gap on one of its finitely many sets. -/
theorem finitelySeparated_of_sum_gap (ev : D → I → ℝ) (S : Set I) (M N : Set D)
    (F : Finset I) (hF : (↑F : Set I) ⊆ S) (c : I → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ m ∈ M, ∀ n ∈ N,
      ε ≤ |(∑ i ∈ F, c i * ev m i) - ∑ i ∈ F, c i * ev n i|) :
    FinitelySeparated ev S M N := by
  classical
  let A := ∑ i ∈ F, |c i|
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let δ := ε / (A+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : δ*(A+1) = ε := div_mul_cancel₀ _ (by linarith : A+1 ≠ 0)
  refine ⟨δ, hδ, F, hF, ?_⟩
  intro m hm n hn
  by_contra h
  push_neg at h
  have hsum : |(∑ i ∈ F, c i * ev m i) - ∑ i ∈ F, c i * ev n i| ≤ A*δ := by
    calc
      _ = |∑ i ∈ F, c i * (ev m i - ev n i)| := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ ∑ i ∈ F, |c i * (ev m i - ev n i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ F, |c i| * δ := Finset.sum_le_sum fun i hi => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (h i hi).le (abs_nonneg _)
      _ = A*δ := (Finset.sum_mul _ _ _).symm
  have hh := hgap m hm n hn
  nlinarith

end ThesisCommon
