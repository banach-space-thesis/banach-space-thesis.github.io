import ThesisCommon.Analysis.RichFamilies

/-! The rich-family intersection principle, Proposition 4.7 of the paper. -/
noncomputable section
open ThesisCommon
namespace PEMS

/-- Proposition 4.7: a countable intersection of rich families of actual
closed separable linear subspaces is rich. -/
theorem rich_family_countable_intersection {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (R : ℕ → Set (Submodule 𝕜 E)) (hR : ∀ n, IsRichFamily (R n)) :
    IsRichFamily (⋂ n, R n) := IsRichFamily.iInter R hR

end PEMS
