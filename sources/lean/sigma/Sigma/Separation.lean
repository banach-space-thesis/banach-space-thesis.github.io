import Sigma.Estimates
import ThesisCommon.Analysis.DualSeparation

/-! Linking the common finite-test lemma to the last contradiction in Section 6. -/
namespace SigmaNonprimarity
open ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nonseparation by test evaluations excludes uniform separation by every
finite linear combination of the tests. The intended tests are simple indicators. -/
theorem no_gap_on_span (e : ℕ → E →L[ℝ] ℝ) (T : Set E) (M N : Set ℕ)
    (h : ¬ FinitelySeparated (fun n t => e n t) T M N) :
    ∀ s ∈ Submodule.span ℝ T, ¬ UniformGap (fun n => e n s) M N := by
  intro s hs hgap
  rcases hgap with ⟨ε, hε, hgap⟩
  exact h (finitelySeparated_of_span_gap e T M N s hs hε hgap)

end SigmaNonprimarity
