import PFP.WCGEllOnePrimarinessProofs
import Mathlib.Analysis.Real.Cardinality

/-! The continuum case uses its proved uncountable cofinality. The anti-CH
assumption is retained exactly as in Corollary 4.6. -/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem corollary_4_6 : Corollary_4_6 𝕜 X := by
  intro hCH hX
  have hΓ : Cardinal.aleph 1 < Cardinal.mk ℝ := by rwa [Cardinal.mk_real]
  have hcof : HasUncountableCofinality ℝ := by
    unfold HasUncountableCofinality
    rw [Cardinal.mk_real, Cardinal.continuum]
    exact Cardinal.lt_cof_power le_rfl (by norm_num)
  exact ⟨fun h => hX.ellOne_isUniformlyPrimary_of_countable_model hΓ h,
    fun h => hX.ellOne_isPrimary_of_countable_model hΓ hcof h⟩

end PFP
