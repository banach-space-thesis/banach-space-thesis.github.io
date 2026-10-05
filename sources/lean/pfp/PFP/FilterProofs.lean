import PFP.FilterStatements
import ThesisCommon.Analysis.FilterFactorization

/-! The full abstract filter criterion, Theorem 6.5. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {Γ : Type u} [Infinite Γ]

theorem theorem_6_5 (F : Filter Γ) [F.NeBot] (K D : ℝ) :
    Theorem_6_5 𝕜 Γ F K D := by
  intro h
  exact ⟨filter_hasCPlusPFP F h, filter_hasUPFP F h⟩

end PFP
