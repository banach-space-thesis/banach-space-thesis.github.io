import JLMS.EssentialNorm
import Mathlib.RingTheory.Congruence.Defs

/-!
# Multiplication on the actual Calkin quotient

The compact-operator submodule is a two-sided ideal. Its existing quotient
relation therefore also respects composition. We retain exactly that relation
when supplying the quotient ring, so the underlying quotient classes agree.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def calkinCongruence : RingCon (E →L[𝕜] E) where
  __ := (compactOperator (RingHom.id 𝕜) E E).quotientRel
  add' := by
    intro S S' T T' hS hT
    rw [Submodule.quotientRel_def] at hS hT ⊢
    have h := IsCompactOperator.add hS hT
    change IsCompactOperator (S + T - (S' + T'))
    convert h using 1
    ext x
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    abel
  mul' := by
    intro S S' T T' hS hT
    rw [Submodule.quotientRel_def] at hS hT ⊢
    have h := IsCompactOperator.add (hS.comp_clm T) (hT.clm_comp S')
    change IsCompactOperator (S * T - S' * T')
    convert h using 1
    ext x
    simp only [Pi.add_apply, Function.comp_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel

instance calkinRing : Ring (Calkin 𝕜 E) :=
  inferInstanceAs (Ring (calkinCongruence (𝕜 := 𝕜) (E := E)).Quotient)

@[simp] theorem calkinMk_mul (S T : E →L[𝕜] E) :
    calkinMk 𝕜 E (S * T) = calkinMk 𝕜 E S * calkinMk 𝕜 E T := rfl

instance calkinScalarTower : IsScalarTower 𝕜 (Calkin 𝕜 E) (Calkin 𝕜 E) where
  smul_assoc c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T =>
        exact congrArg (calkinMk 𝕜 E) (smul_mul_assoc c S T)

instance calkinScalarComm : SMulCommClass 𝕜 (Calkin 𝕜 E) (Calkin 𝕜 E) where
  smul_comm c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T =>
        exact congrArg (calkinMk 𝕜 E) (mul_smul_comm c S T).symm

theorem isCalkinAlgebraNorm_iff (n : Calkin 𝕜 E → ℝ) :
    IsCalkinAlgebraNorm 𝕜 E n ↔ IsAlgebraNorm 𝕜 n := by
  constructor
  · rintro ⟨hn, hm⟩
    refine ⟨hn, fun x y => ?_⟩
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T => exact hm S T
  · rintro ⟨hn, hm⟩
    exact ⟨hn, fun S T => hm (calkinMk 𝕜 E S) (calkinMk 𝕜 E T)⟩

end JLMS
