import SurveyStatements.P2Definitions
import Mathlib.RingTheory.Congruence.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Composition respects equivalence modulo compact operators. -/
def calkinCongruence : RingCon (BoundedOperators X) where
  __ := (CompactOperators X).quotientRel
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
    simp only [Pi.add_apply, Function.comp_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sub_apply, map_sub]
    abel

instance calkinRing : Ring (Calkin X) :=
  inferInstanceAs (Ring (calkinCongruence X).Quotient)

@[simp] theorem calkinQuotient_mul (S T : BoundedOperators X) :
    calkinQuotient X (S * T) = calkinQuotient X S * calkinQuotient X T := rfl

@[simp] theorem calkinQuotient_one : calkinQuotient X 1 = (1 : Calkin X) := rfl

@[simp] theorem calkinQuotient_eq_zero_iff (T : BoundedOperators X) :
    calkinQuotient X T = 0 ↔ IsCompactOperator T :=
  Submodule.Quotient.mk_eq_zero _

theorem calkinQuotient_surjective : Function.Surjective (calkinQuotient X) :=
  Submodule.mkQ_surjective (CompactOperators X)

instance calkinScalarTower : IsScalarTower ℂ (Calkin X) (Calkin X) where
  smul_assoc c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T =>
        exact congrArg (calkinQuotient X) (smul_mul_assoc c S T)

instance calkinScalarComm : SMulCommClass ℂ (Calkin X) (Calkin X) where
  smul_comm c x y := 
    by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T =>
        exact congrArg (calkinQuotient X) (mul_smul_comm c S T).symm

instance calkinAlgebra : Algebra ℂ (Calkin X) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- Multiplication is submultiplicative for the actual quotient norm. -/
theorem calkin_norm_mul_le (x y : Calkin X) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  le_of_forall_pos_le_add fun ε hε => by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) (‖x‖, ‖y‖) :=
      continuous_mul.continuousAt
    have h := (Metric.tendsto_nhds_nhds.mp hcont.tendsto) ε hε
    obtain ⟨δ, hδ, hδbound⟩ := h
    obtain ⟨S, hS, hnS⟩ := Submodule.Quotient.norm_mk_lt x hδ
    obtain ⟨T, hT, hnT⟩ := Submodule.Quotient.norm_mk_lt y hδ
    have hlowS : ‖x‖ ≤ ‖S‖ := by
      simpa only [← hS] using Submodule.Quotient.norm_mk_le (CompactOperators X) S
    have hlowT : ‖y‖ ≤ ‖T‖ := by
      simpa only [← hT] using Submodule.Quotient.norm_mk_le (CompactOperators X) T
    have hpair : dist (‖S‖, ‖T‖) (‖x‖, ‖y‖) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      rw [abs_sub_lt_iff, abs_sub_lt_iff]
      constructor <;> constructor <;> linarith
    have hproduct := hδbound hpair
    rw [Real.dist_eq, abs_sub_lt_iff] at hproduct
    calc
      ‖x * y‖ = ‖calkinQuotient X (S * T)‖ := by
        rw [calkinQuotient_mul]
        exact congrArg norm (congrArg₂ (· * ·) hS hT).symm
      _ ≤ ‖S * T‖ := Submodule.Quotient.norm_mk_le (CompactOperators X) _
      _ ≤ ‖S‖ * ‖T‖ := norm_mul_le _ _
      _ ≤ ‖x‖ * ‖y‖ + ε := by linarith [hproduct.1]

instance calkinSeminormedRing : SeminormedRing (Calkin X) :=
  { calkinRing X, (inferInstance : SeminormedAddCommGroup (Calkin X)) with
    norm_mul_le := calkin_norm_mul_le X }

instance calkinNormedRing [CompleteSpace X] : NormedRing (Calkin X) :=
  { calkinSeminormedRing X, (inferInstance : NormedAddCommGroup (Calkin X)) with }

instance calkinNormedAlgebra : NormedAlgebra ℂ (Calkin X) :=
  { calkinAlgebra X, (inferInstance : NormedSpace ℂ (Calkin X)) with }

/-- The representative-based isomorphism preserves the actual quotient product. -/
theorem CalkinBanachAlgebraIso.map_mul {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] (e : CalkinBanachAlgebraIso X A) (s t : Calkin X) :
    e.toContinuousLinearEquiv (s * t) =
      e.toContinuousLinearEquiv s * e.toContinuousLinearEquiv t := by
  obtain ⟨S, rfl⟩ := calkinQuotient_surjective X s
  obtain ⟨T, rfl⟩ := calkinQuotient_surjective X t
  exact e.map_mul_representatives S T

@[simp] theorem CalkinBanachAlgebraIso.map_one {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] (e : CalkinBanachAlgebraIso X A) :
    e.toContinuousLinearEquiv 1 = 1 := e.map_one_representative

/-- An ordinary algebra equivalence extracted from the statement's isomorphism. -/
def CalkinBanachAlgebraIso.toAlgEquiv {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] (e : CalkinBanachAlgebraIso X A) : Calkin X ≃ₐ[ℂ] A :=
  AlgEquiv.ofLinearEquiv e.toContinuousLinearEquiv.toLinearEquiv
    (CalkinBanachAlgebraIso.map_one X e)
    (CalkinBanachAlgebraIso.map_mul X e)

/-- Conversely, a continuous algebra equivalence supplies the exact statement data. -/
def CalkinBanachAlgebraIso.ofAlgEquiv {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] (e : Calkin X ≃ₐ[ℂ] A)
    (h : Continuous e) (hinv : Continuous e.symm) : CalkinBanachAlgebraIso X A where
  toContinuousLinearEquiv :=
    { e.toLinearEquiv with
      continuous_toFun := h
      continuous_invFun := hinv }
  map_mul_representatives S T := by
    simpa only [calkinQuotient_mul] using e.map_mul (calkinQuotient X S) (calkinQuotient X T)
  map_one_representative := by
    simpa only [calkinQuotient_one] using e.map_one

end SurveyStatements.P2
