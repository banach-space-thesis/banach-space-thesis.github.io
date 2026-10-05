import PFP.FilterExamples
import PFP.FilterProofs
import PFP.FilterRosenthal
import ThesisCommon.Analysis.FilterDiagonalization

/-! Full concrete filter conclusions, on the unchanged source targets. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u) [Infinite Γ]

theorem proposition_6_9 (F : Filter Γ) [F.NeBot] : Proposition_6_9 𝕜 Γ F := by
  intro hF
  exact ⟨hF.primaryForFactorisation F, hF.hasCPlusPFP_two F⟩

theorem example_6_10_general : Example_6_10_general 𝕜 Γ := by
  intro μ hμ _
  have hF := coSmallFilter_largeSetSelfSimilar (Γ := Γ) μ hμ
  exact ⟨hF, hF.hasCPlusPFP_two _⟩

theorem example_6_10 : Example_6_10 𝕜 Γ :=
  ⟨example_6_10_general 𝕜 Γ, example_6_10_cofinite 𝕜 Γ, example_6_10_cocountable 𝕜 Γ⟩

theorem remark_6_11 (F : Filter Γ) [F.NeBot] : Remark_6_11 𝕜 Γ F := by
  intro hF
  exact hF.hasCPlusPFP_two F

end PFP
