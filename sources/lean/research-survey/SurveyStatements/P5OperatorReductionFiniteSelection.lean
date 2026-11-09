import SurveyStatements.P5OperatorReductionRefinedSplitSelection

/-! Actual parent-preserving finite selection with independently assigned
positive tolerances. Individual signed second-moment limits suffice. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finite_positive_tolerance {m : ℕ} (τ : Fin m → ℝ)
    (hτ : ∀ i, 0 < τ i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ τ i := by
  induction m with
  | zero => exact ⟨1, zero_lt_one, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨ε, hε, hbound⟩ := ih (fun i => τ i.succ) (fun i => hτ i.succ)
    refine ⟨min (τ 0) ε, lt_min (hτ 0) hε, ?_⟩
    intro i
    exact Fin.cases (min_le_left _ _) (fun j => (min_le_right _ _).trans (hbound j)) i

theorem exists_refined_split_of_finite_moment_limits {m : ℕ}
    (P : LpHaarFiniteParent) (r : ℕ → ℕ) (hr : StrictMono r)
    (f : (n : ℕ) → Fin m → (Fin (2 ^ n) → Bool) → 𝕜)
    (τ : Fin m → ℝ) (hτ : ∀ i, 0 < τ i) (N : ℕ)
    (hlim : ∀ i, Tendsto (fun k => mean (fun θ => ‖f (r k) i θ‖ ^ 2))
      atTop (𝓝 0)) :
    ∃ S : LpHaarFiniteSplit, ∃ k : ℕ, S.level = r k ∧ N ≤ S.level ∧
      S.parent.set = P.set ∧ ∀ i, ‖f S.level i S.signs‖ < τ i := by
  obtain ⟨ε, hε, hbound⟩ := finite_positive_tolerance τ hτ
  have ht : Tendsto (fun k => ∑ i, mean (fun θ => ‖f (r k) i θ‖ ^ 2))
      atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ => hlim i)
  have hsmall := (tendsto_order.mp ht).2 (ε ^ 2) (sq_pos_of_pos hε)
  obtain ⟨S, k, hlevel, hN, hparent, herror⟩ :=
    exists_refined_split_in_reservoir_with_finite_errors P r hr f N hε hsmall
  exact ⟨S, k, hlevel, hN, hparent, fun i => (herror i).trans_le (hbound i)⟩

end SurveyStatements.P5OperatorReduction
