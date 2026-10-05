import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Order.Basic

/-! Iterating genuinely supplied conditional halves gives nested fragments
with unchanged relative support and a geometric conditional-mass bound. -/
noncomputable section
namespace ThesisCommon
variable {B F : Type*} [PartialOrder B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [PartialOrder F] [IsOrderedModule ℝ F]

theorem exists_iterated_conditional_halves (a : B) (H : B → B) (M : B → F)
    (hhalf : ∀ b : B, b ≤ a → ∃ c : B, c ≤ b ∧ H c = H b ∧ M c ≤ (1/2 : ℝ) • M b) :
    ∃ u : ℕ → B, u 0 = a ∧ (∀ n, u (n+1) ≤ u n) ∧
      (∀ n, u n ≤ a) ∧ (∀ n, H (u n) = H a) ∧
      ∀ n, M (u n) ≤ (1/2 : ℝ)^n • M a := by
  choose c hc hH hM using hhalf
  let step : {b : B // b ≤ a} → {b : B // b ≤ a} := fun b =>
    ⟨c b.val b.property, (hc b.val b.property).trans b.property⟩
  let v : ℕ → {b : B // b ≤ a} := fun n => step^[n] ⟨a, le_rfl⟩
  have hv (n : ℕ) : v (n+1) = step (v n) := Function.iterate_succ_apply' _ _ _
  refine ⟨fun n => (v n).val, rfl, ?_, fun n => (v n).property, ?_, ?_⟩
  · intro n
    change (v (n+1)).val ≤ (v n).val
    rw [hv]
    exact hc _ _
  · intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change H (v (n+1)).val = H a
      rw [hv]
      exact (hH _ _).trans ih
  · intro n
    induction n with
    | zero => simp [v]
    | succ n ih =>
      change M (v (n+1)).val ≤ (1/2 : ℝ)^(n+1) • M a
      rw [hv]
      calc
        M (step (v n)).val ≤ (1/2 : ℝ) • M (v n).val := hM _ _
        _ ≤ (1/2 : ℝ) • ((1/2 : ℝ)^n • M a) := smul_le_smul_of_nonneg_left ih (by norm_num)
        _ = (1/2 : ℝ)^(n+1) • M a := by rw [smul_smul, pow_succ']

end ThesisCommon

