import SurveyStatements.P5BiTreeStabilizationRounds

/-! Positive round errors dominated by every relevant two-parameter edge
error and by the prescribed balancing/root error. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Classical

namespace SurveyStatements.P5.BiTree

theorem finite_positive_lower_bound {A : Type*} [Fintype A]
    (f : A → ℝ) (hf : ∀ a, 0 < f a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a, ε ≤ f a := by
  have hfinite (S : Finset A) (hS : ∀ a ∈ S, 0 < f a) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ S, ε ≤ f a := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, fun a ha => (Finset.not_mem_empty a ha).elim⟩
    | @insert a S ha ih =>
        obtain ⟨ε, hε, hεS⟩ := ih (fun b hb => hS b (Finset.mem_insert_of_mem hb))
        refine ⟨min (f a) ε, lt_min (hS a (Finset.mem_insert_self _ _)) hε, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hεS b hb)
  obtain ⟨ε, hε, hεA⟩ := hfinite Finset.univ (fun a _ => hf a)
  exact ⟨ε, hε, fun a => hεA a (Finset.mem_univ a)⟩

theorem exists_round_error_budget (η : ℕ → ℕ → ℝ)
    (hη : ∀ i j, 0 < η i j) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ (∀ n, ε n ≤ δ / 100) ∧
      ∀ n i j, i ≤ n + 1 → j ≤ n + 1 → ε n ≤ η i j / 100 := by
  let f (n : ℕ) : Option (Fin (n + 2) × Fin (n + 2)) → ℝ
    | none => δ / 100
    | some ij => η ij.1.val ij.2.val / 100
  have hf (n : ℕ) (a : Option (Fin (n + 2) × Fin (n + 2))) : 0 < f n a := by
    cases a with
    | none => exact div_pos hδ (by norm_num)
    | some a => exact div_pos (hη a.1.val a.2.val) (by norm_num)
  have hnext (n : ℕ) := finite_positive_lower_bound (f n) (hf n)
  let ε : ℕ → ℝ := fun n => (hnext n).choose
  refine ⟨ε, fun n => (hnext n).choose_spec.1,
    fun n => (hnext n).choose_spec.2 none, ?_⟩
  intro n i j hi hj
  exact (hnext n).choose_spec.2 (some (⟨i, by omega⟩, ⟨j, by omega⟩))

end SurveyStatements.P5.BiTree
