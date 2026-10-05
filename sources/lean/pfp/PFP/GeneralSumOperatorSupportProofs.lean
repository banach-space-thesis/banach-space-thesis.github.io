import PFP.GeneralSumStatements
import ThesisCommon.Analysis.UncountableSchauderOperatorSupport
import ThesisCommon.Analysis.WCGEllOneSupport

/-! Lemmas 4.14 and 4.15 and both alternatives of Corollary 4.16.
The scalarisation is constructed from actual Hahn–Banach functionals and
the genuine scalar norm-series sum. All targets below are the existing
public manuscript statements, with no extra support hypothesis.
-/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 Γ E X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Lemma 4.14, `lem:scalar-to-vector-support`. -/
theorem lemma_4_14 (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Lemma_4_14 𝕜 Γ E X b := by
  intro hs hscalar T
  exact UncountableSchauderSum.operator_countable_support_of_scalar hscalar T

/-- Lemma 4.15, `lem:operator-countable-general`. -/
theorem lemma_4_15 (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Lemma_4_15 𝕜 Γ E X b := by
  intro hs hsep T Δ hΔ
  exact UncountableSchauderSum.countable_block_support_of_separable_scalar_ranges
    hsep T Δ hΔ

/-- The full separable alternative of Corollary 4.16. -/
theorem corollary_4_16_separable (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Corollary_4_16_separable 𝕜 Γ E X b := by
  intro hs hsep T Δ hΔ
  letI := hsep
  exact UncountableSchauderSum.countable_block_support_of_separable T Δ hΔ

/-- The WCG alternative of Corollary 4.16 on actual ℓ₁(Γ,X), over either
scalar field and every index type. -/
theorem corollary_4_16_ellOne : Corollary_4_16_ellOne 𝕜 Γ X := by
  intro hX T Δ hΔ
  exact hX.ellOne_countable_block_support T Δ hΔ

/-- Full Corollary 4.16, `cor:operator-countable`, with both alternatives. -/
theorem corollary_4_16 (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Corollary_4_16 𝕜 Γ E X b :=
  ⟨corollary_4_16_separable 𝕜 Γ E X b, corollary_4_16_ellOne 𝕜 Γ X⟩

end PFP
