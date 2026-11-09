import SurveyStatements.P5OperatorReductionFiniteSelection

/-! Candidate packets at absolute levels, and finite scalar constraints on
the actual split itself. Low levels are discarded before selection. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

def candidateRefinedSplit (P : LpHaarFiniteParent) (n : ℕ)
    (θ : Fin (2 ^ n) → Bool) : LpHaarFiniteSplit :=
  if hn : P.level ≤ n then refinedFiniteSplit P n hn θ
  else ⟨P.level, P.atoms, fun _ => false, P.nonempty⟩

theorem candidateRefinedSplit_eq (P : LpHaarFiniteParent) (n : ℕ)
    (hn : P.level ≤ n) (θ : Fin (2 ^ n) → Bool) :
    candidateRefinedSplit P n θ = refinedFiniteSplit P n hn θ := by
  simp only [candidateRefinedSplit, dif_pos hn]

theorem exists_candidate_split_of_actual_error_moment_limits {I : Type*} [Fintype I]
    (P : LpHaarFiniteParent) (r : ℕ → ℕ) (hr : StrictMono r)
    (error : I → LpHaarFiniteSplit → 𝕜) (τ : I → ℝ)
    (hτ : ∀ i, 0 < τ i) (N : ℕ)
    (hlim : ∀ i, Tendsto (fun k => mean (fun θ =>
      ‖error i (candidateRefinedSplit P (r k) θ)‖ ^ 2)) atTop (𝓝 0)) :
    ∃ S : LpHaarFiniteSplit, ∃ k : ℕ, S.level = r k ∧ N ≤ S.level ∧
      S.parent.set = P.set ∧ ∀ i, ‖error i S‖ < τ i := by
  let e := Fintype.equivFin I
  obtain ⟨ε, hε, hbound⟩ := finite_positive_tolerance
    (fun i => τ (e.symm i)) (fun i => hτ (e.symm i))
  have ht : Tendsto (fun k => ∑ i : Fin (Fintype.card I), mean (fun θ =>
      ‖error (e.symm i) (candidateRefinedSplit P (r k) θ)‖ ^ 2)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ => hlim (e.symm i))
  have hsmall := (tendsto_order.mp ht).2 (ε ^ 2) (sq_pos_of_pos hε)
  have hlate : ∀ᶠ k in atTop, max N P.level ≤ r k :=
    hr.tendsto_atTop.eventually (eventually_ge_atTop (max N P.level))
  obtain ⟨k, hk, hm⟩ := (hlate.and hsmall).exists
  obtain ⟨θ, hθ⟩ := finite_sign_simultaneous_small
    (fun i θ => error (e.symm i) (candidateRefinedSplit P (r k) θ)) hε hm
  have hP : P.level ≤ r k := (le_max_right N P.level).trans hk
  refine ⟨candidateRefinedSplit P (r k) θ, k, ?_, ?_, ?_, ?_⟩
  · rw [candidateRefinedSplit_eq P _ hP]
    rfl
  · rw [candidateRefinedSplit_eq P _ hP]
    exact (le_max_left N P.level).trans hk
  · rw [candidateRefinedSplit_eq P _ hP]
    exact refinedFiniteSplit_parent P _ hP θ
  · intro i
    simpa only [e.symm_apply_apply] using (hθ (e i)).trans_le (hbound (e i))

end SurveyStatements.P5OperatorReduction
