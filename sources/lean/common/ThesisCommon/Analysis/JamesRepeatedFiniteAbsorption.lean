import ThesisCommon.Analysis.JamesFiniteSectionAbsorption
import ThesisCommon.Analysis.LpFamilyProducts
import ThesisCommon.Analysis.RepeatedSpaceAbsorption
import Mathlib.Data.Nat.Pairing

/-! James space absorbs a countable repetition of any genuine finite-section
sum, and consequently every bounded retract of such a sum. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesRepeatedFiniteSectionAbsorption (lengths : ℕ → ℕ) :
    JamesSequenceSpace 𝕜 p ≃L[𝕜] JamesSequenceSpace 𝕜 p ×
      lp (fun _ : ℕ => JamesFiniteSectionSum (𝕜 := 𝕜) p lengths) p.val := by
  have hq : 0 < p.val.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  let e := lpFamilyProductReindexIsometry (𝕜 := 𝕜)
    (E := fun n => JamesInitialBlock 𝕜 p (lengths n)) p.val hq Nat.pairEquiv
  exact (jamesFiniteSectionAbsorption (𝕜 := 𝕜) p hp
    (fun k => lengths (Nat.pairEquiv.symm k).2)).trans
      ((ContinuousLinearEquiv.refl 𝕜 (JamesSequenceSpace 𝕜 p)).prodCongr e.toContinuousLinearEquiv.symm)

def jamesAbsorbRetractOfFiniteSectionSum (lengths : ℕ → ℕ)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (J : Z →L[𝕜] JamesFiniteSectionSum (𝕜 := 𝕜) p lengths)
    (Q : JamesFiniteSectionSum (𝕜 := 𝕜) p lengths →L[𝕜] Z)
    (hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 Z) :
    JamesSequenceSpace 𝕜 p ≃L[𝕜] JamesSequenceSpace 𝕜 p × Z :=
  absorbComplementedOfRepeatedAbsorption p.val
    (jamesRepeatedFiniteSectionAbsorption (𝕜 := 𝕜) p hp lengths) J Q hQJ

end ThesisCommon
