import PFP.JamesGeneralDualProofs
import ThesisCommon.Analysis.JamesPrimariness

/-! Both clauses of Appendix B.4 on the actual James spaces. The classical
primariness input is now proved using actual sampling factors and finite-section
absorption; the source's general-p clause retains its stated hypothesis. -/
noncomputable section
namespace PFP
open ThesisCommon
open scoped ENNReal

theorem theorem_B_4_classical (𝕜 : Type*) [RCLike 𝕜] : Theorem_B_4_classical 𝕜 := by
  let p₂ : BanachExponent := ⟨2, by norm_num⟩
  change IsPrimary 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p₂))
  have hp₂ : p₂.val ≠ ∞ := by norm_num [p₂]
  exact theorem_B_4_general 𝕜 p₂ (by norm_num [p₂]) hp₂
    (jamesSequence_primary p₂ hp₂ (by norm_num [p₂]))

/-- Source label `thm:Jp-dual-primary`, with both original conclusions. -/
theorem theorem_B_4 (𝕜 : Type*) [RCLike 𝕜] : Theorem_B_4 𝕜 :=
  ⟨fun p => theorem_B_4_general 𝕜 p, theorem_B_4_classical 𝕜⟩

end PFP
