import PFP.UncountableStatements
import ThesisCommon.Analysis.SeparableLpPrimaryTransfer

/-! The full finite-p separable clause of Theorem 4.1(ii), with both the
uniform and uncountable-cofinality alternatives. -/
noncomputable section
open scoped Cardinal ENNReal
namespace PFP
open ThesisCommon TopologicalSpace
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem theorem_4_1_lp (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hsep : SeparableSpace X) (p : BanachExponent) (hp : 1 < p.val) (hfin : p.val ≠ ∞) :
    PrimarinessTransfer 𝕜 (SequenceSum p X) (lp (fun _ : Γ => X) p.val) Γ := by
  letI := hsep
  have hpReal : 1 < p.val.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hfin).mpr hp
  constructor
  · intro h
    have h' := lp_isUniformlyPrimary_of_countable_model p.val hpReal hfin hΓ h
    exact ⟨h'.isPrimary, h'⟩
  · intro h hcof
    exact lp_isPrimary_of_countable_model p.val hpReal hfin hΓ hcof h

end PFP
