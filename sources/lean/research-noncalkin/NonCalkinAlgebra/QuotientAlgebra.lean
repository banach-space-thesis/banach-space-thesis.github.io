import NonCalkinAlgebra.OperatorIdealMultiplication
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def operatorCongruence (convention : QuotientConvention) : RingCon (BoundedOperators X) where
  __ := (operatorIdeal X convention).quotientRel
  add' := by
    intro S S' T T' hS hT
    rw [Submodule.quotientRel_def] at hS hT ⊢
    have h := (operatorIdeal X convention).add_mem hS hT
    convert h using 1
    ext x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    abel
  mul' := by
    intro S S' T T' hS hT
    rw [Submodule.quotientRel_def] at hS hT ⊢
    have h := (operatorIdeal X convention).add_mem
      (operatorIdeal_mul_right X convention (S - S') T hS)
      (operatorIdeal_mul_left X convention S' (T - T') hT)
    convert h using 1
    ext x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.mul_apply, map_sub]
    abel

instance operatorQuotientRing (convention : QuotientConvention) :
    Ring (OperatorQuotient X convention) :=
  inferInstanceAs (Ring (operatorCongruence X convention).Quotient)

@[simp] theorem operatorQuotientMap_mul (convention : QuotientConvention)
    (S T : BoundedOperators X) :
    operatorQuotientMap X convention (S * T) =
      operatorQuotientMap X convention S * operatorQuotientMap X convention T := rfl

@[simp] theorem operatorQuotientMap_one (convention : QuotientConvention) :
    operatorQuotientMap X convention 1 = (1 : OperatorQuotient X convention) := rfl

@[simp] theorem operatorQuotientMap_eq_zero (convention : QuotientConvention)
    (T : BoundedOperators X) :
    operatorQuotientMap X convention T = 0 ↔ T ∈ operatorIdeal X convention :=
  Submodule.Quotient.mk_eq_zero _

theorem operatorQuotientMap_surjective (convention : QuotientConvention) :
    Function.Surjective (operatorQuotientMap X convention) :=
  Submodule.mkQ_surjective _

instance operatorQuotientScalarTower (convention : QuotientConvention) :
    IsScalarTower ℂ (OperatorQuotient X convention) (OperatorQuotient X convention) where
  smul_assoc c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T => exact congrArg (operatorQuotientMap X convention) (smul_mul_assoc c S T)

instance operatorQuotientScalarComm (convention : QuotientConvention) :
    SMulCommClass ℂ (OperatorQuotient X convention) (OperatorQuotient X convention) where
  smul_comm c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T => exact congrArg (operatorQuotientMap X convention) (mul_smul_comm c S T).symm

instance operatorQuotientAlgebra (convention : QuotientConvention) :
    Algebra ℂ (OperatorQuotient X convention) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem operatorQuotient_norm_mul_le (convention : QuotientConvention)
    (x y : OperatorQuotient X convention) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  le_of_forall_pos_le_add fun ε hε => by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) (‖x‖, ‖y‖) :=
      continuous_mul.continuousAt
    obtain ⟨δ, hδ, hδbound⟩ := (Metric.tendsto_nhds_nhds.mp hcont.tendsto) ε hε
    obtain ⟨S, hS, hnS⟩ := Submodule.Quotient.norm_mk_lt x hδ
    obtain ⟨T, hT, hnT⟩ := Submodule.Quotient.norm_mk_lt y hδ
    have hlowS : ‖x‖ ≤ ‖S‖ := by
      simpa only [← hS] using Submodule.Quotient.norm_mk_le (operatorIdeal X convention) S
    have hlowT : ‖y‖ ≤ ‖T‖ := by
      simpa only [← hT] using Submodule.Quotient.norm_mk_le (operatorIdeal X convention) T
    have hp : dist (‖S‖, ‖T‖) (‖x‖, ‖y‖) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      rw [abs_sub_lt_iff, abs_sub_lt_iff]
      constructor <;> constructor <;> linarith
    have hproduct := hδbound hp
    rw [Real.dist_eq, abs_sub_lt_iff] at hproduct
    calc
      ‖x * y‖ = ‖operatorQuotientMap X convention (S * T)‖ := by
        rw [operatorQuotientMap_mul]
        exact congrArg norm (congrArg₂ (· * ·) hS hT).symm
      _ ≤ ‖S * T‖ := Submodule.Quotient.norm_mk_le (operatorIdeal X convention) _
      _ ≤ ‖S‖ * ‖T‖ := norm_mul_le _ _
      _ ≤ ‖x‖ * ‖y‖ + ε := by linarith [hproduct.1]

instance operatorQuotientSeminormedRing (convention : QuotientConvention) :
    SeminormedRing (OperatorQuotient X convention) :=
  { operatorQuotientRing X convention,
      (inferInstance : SeminormedAddCommGroup (OperatorQuotient X convention)) with
    norm_mul_le := operatorQuotient_norm_mul_le X convention }

instance operatorQuotientNormedRing (convention : QuotientConvention) :
    NormedRing (OperatorQuotient X convention) :=
  { operatorQuotientSeminormedRing X convention,
      (inferInstance : NormedAddCommGroup (OperatorQuotient X convention)) with }

instance operatorQuotientNormedAlgebra (convention : QuotientConvention) :
    NormedAlgebra ℂ (OperatorQuotient X convention) :=
  { operatorQuotientAlgebra X convention,
      (inferInstance : NormedSpace ℂ (OperatorQuotient X convention)) with }

end NonCalkinAlgebra
