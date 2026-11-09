import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Continuum

/-! The exact large cardinal used in the source's second construction. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P2

/-- The source's `λ = beth_ω`. -/
def bethOmega : Cardinal := Cardinal.beth Ordinal.omega0

/-- A set of letters of the required cardinality. -/
def LargeAlphabet : Type := bethOmega.out

@[simp] theorem mk_largeAlphabet : Cardinal.mk LargeAlphabet = bethOmega :=
  Cardinal.mk_out bethOmega

theorem bethOmega_isStrongLimit : Cardinal.IsStrongLimit bethOmega :=
  Cardinal.isStrongLimit_beth.mpr Ordinal.isSuccLimit_omega0.isSuccPrelimit

theorem continuum_lt_bethOmega : Cardinal.continuum < bethOmega := by
  change Cardinal.continuum < Cardinal.beth Ordinal.omega0
  simpa only [Cardinal.beth_one] using Cardinal.isNormal_beth.strictMono Ordinal.one_lt_omega0

/-- The cardinal-arithmetic conclusion of the source's density trap. -/
theorem bethOmega_le_of_le_two_power (κ : Cardinal) (h : bethOmega ≤ 2 ^ κ) :
    bethOmega ≤ κ := by
  by_contra hbad
  exact not_lt_of_ge h (bethOmega_isStrongLimit.two_power_lt (lt_of_not_ge hbad))

end SurveyStatements.P2
