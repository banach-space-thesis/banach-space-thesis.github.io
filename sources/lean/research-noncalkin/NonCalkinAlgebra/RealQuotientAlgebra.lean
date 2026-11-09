import NonCalkinAlgebra.RealOperatorIdealMultiplication
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

def realOperatorCongruence (convention : QuotientConvention) : RingCon ((X →L[ℝ] X)) where
  __ := (realOperatorIdeal X convention).quotientRel
  add' := by
    intro S S' T T' hS hT
    rw [Submodule.quotientRel_def] at hS hT ⊢
    have h := (realOperatorIdeal X convention).add_mem hS hT
    convert h using 1
    ext x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    abel
  mul' := by
    intro S S' T T' hS hT
    rw [Submodule.quotientRel_def] at hS hT ⊢
    have h := (realOperatorIdeal X convention).add_mem
      (realOperatorIdeal_mul_right X convention (S - S') T hS)
      (realOperatorIdeal_mul_left X convention S' (T - T') hT)
    convert h using 1
    ext x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.mul_apply, map_sub]
    abel

instance realOperatorQuotientRing (convention : QuotientConvention) :
    Ring (RealOperatorQuotient X convention) :=
  inferInstanceAs (Ring (realOperatorCongruence X convention).Quotient)

@[simp] theorem realOperatorQuotientMap_mul (convention : QuotientConvention)
    (S T : (X →L[ℝ] X)) :
    realOperatorQuotientMap X convention (S * T) =
      realOperatorQuotientMap X convention S * realOperatorQuotientMap X convention T := rfl

@[simp] theorem realOperatorQuotientMap_one (convention : QuotientConvention) :
    realOperatorQuotientMap X convention 1 = (1 : RealOperatorQuotient X convention) := rfl

@[simp] theorem realOperatorQuotientMap_eq_zero (convention : QuotientConvention)
    (T : (X →L[ℝ] X)) :
    realOperatorQuotientMap X convention T = 0 ↔ T ∈ realOperatorIdeal X convention :=
  Submodule.Quotient.mk_eq_zero _

theorem realOperatorQuotientMap_surjective (convention : QuotientConvention) :
    Function.Surjective (realOperatorQuotientMap X convention) :=
  Submodule.mkQ_surjective _

instance realOperatorQuotientScalarTower (convention : QuotientConvention) :
    IsScalarTower ℝ (RealOperatorQuotient X convention) (RealOperatorQuotient X convention) where
  smul_assoc c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T => exact congrArg (realOperatorQuotientMap X convention) (smul_mul_assoc c S T)

instance realOperatorQuotientScalarComm (convention : QuotientConvention) :
    SMulCommClass ℝ (RealOperatorQuotient X convention) (RealOperatorQuotient X convention) where
  smul_comm c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T => exact congrArg (realOperatorQuotientMap X convention) (mul_smul_comm c S T).symm

instance realOperatorQuotientAlgebra (convention : QuotientConvention) :
    Algebra ℝ (RealOperatorQuotient X convention) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem realOperatorQuotient_norm_mul_le (convention : QuotientConvention)
    (x y : RealOperatorQuotient X convention) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  le_of_forall_pos_le_add fun ε hε => by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) (‖x‖, ‖y‖) :=
      continuous_mul.continuousAt
    obtain ⟨δ, hδ, hδbound⟩ := (Metric.tendsto_nhds_nhds.mp hcont.tendsto) ε hε
    obtain ⟨S, hS, hnS⟩ := Submodule.Quotient.norm_mk_lt x hδ
    obtain ⟨T, hT, hnT⟩ := Submodule.Quotient.norm_mk_lt y hδ
    have hlowS : ‖x‖ ≤ ‖S‖ := by
      simpa only [← hS] using Submodule.Quotient.norm_mk_le (realOperatorIdeal X convention) S
    have hlowT : ‖y‖ ≤ ‖T‖ := by
      simpa only [← hT] using Submodule.Quotient.norm_mk_le (realOperatorIdeal X convention) T
    have hp : dist (‖S‖, ‖T‖) (‖x‖, ‖y‖) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      rw [abs_sub_lt_iff, abs_sub_lt_iff]
      constructor <;> constructor <;> linarith
    have hproduct := hδbound hp
    rw [Real.dist_eq, abs_sub_lt_iff] at hproduct
    calc
      ‖x * y‖ = ‖realOperatorQuotientMap X convention (S * T)‖ := by
        rw [realOperatorQuotientMap_mul]
        exact congrArg norm (congrArg₂ (· * ·) hS hT).symm
      _ ≤ ‖S * T‖ := Submodule.Quotient.norm_mk_le (realOperatorIdeal X convention) _
      _ ≤ ‖S‖ * ‖T‖ := norm_mul_le _ _
      _ ≤ ‖x‖ * ‖y‖ + ε := by linarith [hproduct.1]

instance realOperatorQuotientSeminormedRing (convention : QuotientConvention) :
    SeminormedRing (RealOperatorQuotient X convention) :=
  { realOperatorQuotientRing X convention,
      (inferInstance : SeminormedAddCommGroup (RealOperatorQuotient X convention)) with
    norm_mul_le := realOperatorQuotient_norm_mul_le X convention }

instance realOperatorQuotientNormedRing (convention : QuotientConvention) :
    NormedRing (RealOperatorQuotient X convention) :=
  { realOperatorQuotientSeminormedRing X convention,
      (inferInstance : NormedAddCommGroup (RealOperatorQuotient X convention)) with }

instance realOperatorQuotientNormedAlgebra (convention : QuotientConvention) :
    NormedAlgebra ℝ (RealOperatorQuotient X convention) :=
  { realOperatorQuotientAlgebra X convention,
      (inferInstance : NormedSpace ℝ (RealOperatorQuotient X convention)) with }

end NonCalkinAlgebra
