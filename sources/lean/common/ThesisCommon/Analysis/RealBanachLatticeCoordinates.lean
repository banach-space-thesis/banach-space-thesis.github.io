import ThesisCommon.ALSpace
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! In a real Banach-lattice model the real form is the entire ambient
space, with its genuine inherited norm. -/
noncomputable section
namespace ThesisCommon.BanachLatticeModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (B : BanachLatticeModel ℝ E)

theorem coe_realPart_real (x : E) : (B.realPart x : E) = x := by
  simpa only [RCLike.I_to_real, zero_smul, add_zero] using (B.decomposition x).symm

def realFormLinearIsometryEquiv : B.realForm ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective B.realForm.subtypeₗᵢ
    (fun x => ⟨B.realPart x, B.coe_realPart_real x⟩)

theorem realFormLinearIsometryEquiv_apply (x : B.realForm) :
    B.realFormLinearIsometryEquiv x = (x : E) := rfl

end ThesisCommon.BanachLatticeModel
