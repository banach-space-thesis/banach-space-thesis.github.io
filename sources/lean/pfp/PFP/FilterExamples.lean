import PFP.FilterStatements
import ThesisCommon.Analysis.FilterConvergenceExamples

/-! Checked parts of Example 6.10. The co-small self-similarity and both
space identifications are proved here. Its PFP assertion still requires
the separate large-set self-similarity theorem, Proposition 6.9. -/
noncomputable section
namespace PFP
open ThesisCommon
open scoped ENNReal Cardinal
universe u
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u) [Infinite Γ]

omit [Infinite Γ] in
theorem example_6_10_self_similarity (μ : Cardinal.{u})
    (hμ : Cardinal.aleph0 ≤ μ) :
    IsLargeSetSelfSimilarFilter (coSmallFilter (Γ := Γ) μ hμ) :=
  coSmallFilter_largeSetSelfSimilar μ hμ

theorem example_6_10_cofinite : Example_6_10_cofinite 𝕜 Γ := by
  refine ⟨coSmallFilter_aleph0, ?_⟩
  intro x
  rw [coSmallFilter_aleph0]
  exact mem_cofinite_filterNull_iff x

theorem example_6_10_cocountable : Example_6_10_cocountable 𝕜 Γ := by
  intro _ x
  exact mem_cocountable_filterNull_iff x

end PFP
