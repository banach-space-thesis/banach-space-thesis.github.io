import ThesisCommon.Analysis.NormingSequence
import Mathlib.Tactic.NormNum

/-! Executable checks of source discrepancies, not proofs of the main theorem. -/
namespace SigmaNonprimarity.SourceChecks
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Literal inequality printed in Definition 3.2. Kept separate from IsCNorming. -/
def PrintedCNorming (e : ℕ → E →L[ℝ] ℝ) (c : ℝ) : Prop :=
  0 < c ∧ c ≤ 1 ∧ (∀ n, ‖e n‖ ≤ 1) ∧ ∀ x, c * (⨆ n, |e n x|) ≤ ‖x‖

/-- The printed definition admits the zero sequence on every space. -/
theorem zero_printedCNorming : PrintedCNorming E (fun _ => 0) 1 := by
  refine ⟨by norm_num, le_rfl, by simp, ?_⟩
  intro x
  simp [norm_nonneg x]

/-- DP would be false for every space if Definition 3.2 were read literally. -/
theorem printed_desiredProperty_impossible :
    ¬ (∀ e : ℕ → E →L[ℝ] ℝ, (∃ c, PrintedCNorming E e c) →
      ∃ f : E, ¬ ∃ g : E, ∀ n, e n g = |e n f|) := by
  intro h
  obtain ⟨f, hf⟩ := h (fun _ => 0) ⟨1, zero_printedCNorming E⟩
  exact hf ⟨0, by simp⟩

/-- A numerical counterexample to the δ(4r+3) bound printed in equation (8).
Here r=0, δ=1/10, v=2, u=229/100 and z=238/100. -/
theorem printed_equation_8_bound_fails :
    |(229/100 : ℝ) - 2| < 3*(1/10) ∧
    abs (|(229/100 : ℝ)| - (0*(229/100) + 238/100)) < 1/10 ∧
    ¬ abs (|(2 : ℝ)| - (0*2 + 238/100)) < (1/10)*(4*0+3) := by
  norm_num

end SigmaNonprimarity.SourceChecks
