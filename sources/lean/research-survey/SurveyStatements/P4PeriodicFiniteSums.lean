import SurveyStatements.P4FiniteFrame
import Mathlib.Algebra.BigOperators.Fin

/-! Exact block decomposition of finite sums of a periodic sequence. -/

noncomputable section
set_option autoImplicit false

open Finset

namespace SurveyStatements.P4

lemma periodic_nat_mul_add {A : Type*} {N : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + N) = f i) (r i : ℕ) : f (r * N + i) = f i := by
  induction r with
  | zero => simp
  | succ r hr =>
      rw [Nat.succ_mul]
      have heq : r * N + N + i = (r * N + i) + N := by omega
      rw [heq, hf, hr]

lemma sum_periodic_nat_blocks {A : Type*} [AddCommMonoid A] {N : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + N) = f i) (r : ℕ) :
    ∑ i ∈ range (r * N), f i = r • ∑ i ∈ range N, f i := by
  induction r with
  | zero => simp
  | succ r hr =>
      rw [Nat.succ_mul, sum_range_add, hr]
      have heq : (∑ i ∈ range N, f (r * N + i)) = ∑ i ∈ range N, f i := by
        apply sum_congr rfl
        intro i hi
        exact periodic_nat_mul_add f hf r i
      rw [heq, succ_nsmul]

lemma sum_periodic_nat_prefix {A : Type*} [AddCommMonoid A] {N : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + N) = f i) (r t : ℕ) :
    ∑ i ∈ range (r * N + t), f i =
      r • (∑ i ∈ range N, f i) + ∑ i ∈ range t, f i := by
  rw [sum_range_add, sum_periodic_nat_blocks f hf r]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact periodic_nat_mul_add f hf r i

end SurveyStatements.P4
