import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Countably many mutually orthogonal copies from two copies

The relations vᵢuⱼ = δᵢⱼ give the algebraic part of a Banach-space square
decomposition. Iterating the first copy and taking the second copy at each
stage yields countably many disjoint copies of the original space.
-/

namespace JLMS
variable {B : Type*} [Ring B]

theorem exists_orthogonalCopies (u₀ u₁ v₀ v₁ : B)
    (h₀₀ : v₀ * u₀ = 1) (h₁₁ : v₁ * u₁ = 1)
    (h₀₁ : v₀ * u₁ = 0) (h₁₀ : v₁ * u₀ = 0) :
    ∃ u v : ℕ → B, ∀ n m, v n * u m = if n = m then 1 else 0 := by
  let u : ℕ → B := fun n => u₀ ^ n * u₁
  let v : ℕ → B := fun n => v₁ * v₀ ^ n
  have hu (n) : u (n + 1) = u₀ * u n := by simp [u, pow_succ', mul_assoc]
  have hv (n) : v (n + 1) = v n * v₀ := by simp [v, pow_succ, mul_assoc]
  refine ⟨u, v, ?_⟩
  intro n
  induction n with
  | zero =>
    intro m
    cases m with
    | zero => simp [u, v, h₁₁]
    | succ m => simp [hu, v, ← mul_assoc, h₁₀]
  | succ n ih =>
    intro m
    cases m with
    | zero => simp [hv, u, mul_assoc, h₀₁]
    | succ m =>
      rw [hv, hu]
      calc
        v n * v₀ * (u₀ * u m) = v n * (v₀ * u₀) * u m := by simp only [mul_assoc]
        _ = v n * u m := by rw [h₀₀, mul_one]
        _ = if n + 1 = m + 1 then 1 else 0 := by simpa using ih m

end JLMS
