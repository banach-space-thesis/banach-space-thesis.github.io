import SurveyStatements.P5OperatorReductionConcreteErrorLists

/-! A newly born distinct pair contains exactly one fresh split. The
finite-history formulation therefore inherits the two one-sided moments. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem bornDistinctPair_cases {n : ℕ} (v : BornDistinctPair n) :
    ∃ j : Fin n, v.val = (Fin.last n, j.castSucc) ∨
      v.val = (j.castSucc, Fin.last n) := by
  rcases v with ⟨⟨i, j⟩, hij, hborn⟩
  rcases hborn with hi | hj
  · have hi' : i = Fin.last n := Fin.ext hi
    subst i
    have hj' : j.val < n := by
      have hval : j.val ≠ n := by
        intro h
        exact hij (Fin.ext h.symm)
      omega
    refine ⟨⟨j.val, hj'⟩, Or.inl ?_⟩
    rfl
  · have hj' : j = Fin.last n := Fin.ext hj
    subst j
    have hi' : i.val < n := by
      have hval : i.val ≠ n := by
        intro h
        exact hij (Fin.ext h)
      omega
    refine ⟨⟨i.val, hi'⟩, Or.inr ?_⟩
    rfl

theorem born_pair_moment_tendsto_zero {n : ℕ}
    (F : LpHaarFiniteSplit → LpHaarFiniteSplit → 𝕜)
    (h : Fin n → LpHaarFiniteSplit) (P : LpHaarFiniteParent)
    (ht : ∀ j, Tendsto (fun m => mean (fun θ : Fin (2 ^ m) → Bool =>
      ‖F (candidateRefinedSplit P m θ) (h j)‖ ^ 2)) atTop (𝓝 0))
    (hs : ∀ j, Tendsto (fun m => mean (fun θ : Fin (2 ^ m) → Bool =>
      ‖F (h j) (candidateRefinedSplit P m θ)‖ ^ 2)) atTop (𝓝 0))
    (v : BornDistinctPair n) :
    Tendsto (fun m => mean (fun θ : Fin (2 ^ m) → Bool =>
      ‖F (currentSplitHistory h (candidateRefinedSplit P m θ) v.val.1)
        (currentSplitHistory h (candidateRefinedSplit P m θ) v.val.2)‖ ^ 2))
      atTop (𝓝 0) := by
  obtain ⟨j, hj | hj⟩ := bornDistinctPair_cases v
  · simpa only [hj, currentSplitHistory, Fin.lastCases_last, Fin.lastCases_castSucc] using ht j
  · simpa only [hj, currentSplitHistory, Fin.lastCases_last, Fin.lastCases_castSucc] using hs j

end SurveyStatements.P5OperatorReduction
