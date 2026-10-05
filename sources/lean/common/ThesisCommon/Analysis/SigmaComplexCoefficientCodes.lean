import ThesisCommon.Analysis.CountableCoefficientCodes
import Mathlib.Analysis.Complex.Basic

/-! Countable complex coefficient codes still have cardinal at most continuum.
Encode real and imaginary parts by the existing real countable-code theorem. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon

theorem complex_lp_one_countable_support {ι : Type*} (f : lp (fun _ : ι => ℂ) 1) :
    (Function.support f).Countable := by
  have hs : Summable (fun i => ‖f i‖) := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      (lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) f).summable
  simpa only [Function.support,norm_ne_zero_iff] using hs.countable_support

theorem complex_lp_one_cardinal_le_continuum {ι : Type} [Nonempty ι] (hι : #ι ≤ 𝔠) :
    #(lp (fun _ : ι => ℂ) 1) ≤ 𝔠 := by
  have hre (f : lp (fun _ : ι => ℂ) 1) : (Function.support (fun i => (f i).re)).Countable := by
    apply (complex_lp_one_countable_support f).mono
    intro i hi hz
    exact hi (by change (f i).re = 0; rw [hz,Complex.zero_re])
  have him (f : lp (fun _ : ι => ℂ) 1) : (Function.support (fun i => (f i).im)).Countable := by
    apply (complex_lp_one_countable_support f).mono
    intro i hi hz
    exact hi (by change (f i).im = 0; rw [hz,Complex.zero_im])
  let encode : lp (fun _ : ι => ℂ) 1 → CountableCoefficientCode ι × CountableCoefficientCode ι :=
    fun f => (⟨fun i => (f i).re,hre f⟩,⟨fun i => (f i).im,him f⟩)
  have hinj : Function.Injective encode := by
    intro f g h
    apply lp.ext
    funext i
    apply Complex.ext
    · exact congrArg (fun z : CountableCoefficientCode ι × CountableCoefficientCode ι => z.1.val i) h
    · exact congrArg (fun z : CountableCoefficientCode ι × CountableCoefficientCode ι => z.2.val i) h
  have hc := countableCoefficientCode_cardinal_le hι
  apply (Cardinal.mk_le_of_injective hinj).trans
  rw [Cardinal.mk_prod]
  simpa only [Cardinal.lift_id,Cardinal.continuum_mul_self] using mul_le_mul' hc hc

end ThesisCommon
