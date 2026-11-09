import SurveyStatements.P2ShiftQuotient
import SurveyStatements.P2Calkin

/-! A cardinality form of the source's large-space obstruction.

The separated family already suffices to rule out spaces of cardinality at
most the continuum; no restriction on the universe of the Banach space is used.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem mk_calkin_le_power_self :
    Cardinal.mk (Calkin X) ≤ Cardinal.mk X ^ Cardinal.mk X := by
  calc
    Cardinal.mk (Calkin X) ≤ Cardinal.mk (BoundedOperators X) :=
      Cardinal.mk_le_of_surjective (calkinQuotient_surjective X)
    _ ≤ Cardinal.mk (X → X) := Cardinal.mk_le_of_injective
      (show Function.Injective (fun T : BoundedOperators X => (T : X → X)) from
        fun S T h => ContinuousLinearMap.ext (congrFun h))
    _ = Cardinal.mk X ^ Cardinal.mk X := by simp only [Cardinal.mk_arrow, Cardinal.lift_id]

theorem mk_calkin_le_two_power_continuum
    (hX : Cardinal.mk X ≤ Cardinal.continuum) :
    Cardinal.mk (Calkin X) ≤ 2 ^ Cardinal.continuum := by
  calc
    Cardinal.mk (Calkin X) ≤ Cardinal.mk X ^ Cardinal.mk X := mk_calkin_le_power_self X
    _ ≤ Cardinal.continuum ^ Cardinal.mk X := Cardinal.power_le_power_right hX
    _ ≤ Cardinal.continuum ^ Cardinal.continuum :=
      Cardinal.power_le_power_left Cardinal.continuum_ne_zero hX
    _ = 2 ^ Cardinal.continuum := Cardinal.power_self_eq Cardinal.aleph0_le_continuum

/-- Any Calkin representation of this actual quotient has an underlying space
of cardinality strictly larger than the continuum. -/
theorem continuum_lt_mk_of_large_calkinIso
    {A : Type} [NormedRing A] [NormedAlgebra ℂ A]
    (hA : bethOmega ≤ Cardinal.mk A) (e : CalkinBanachAlgebraIso X A) :
    Cardinal.continuum < Cardinal.mk X := by
  by_contra hbad
  have hX := le_of_not_gt hbad
  have hlarge : Cardinal.lift.{v} bethOmega.{0} ≤ Cardinal.mk (Calkin X) := by
    calc
      Cardinal.lift.{v} bethOmega.{0} ≤
          Cardinal.lift.{v} (Cardinal.mk A) := Cardinal.lift_le.mpr hA
      _ = Cardinal.mk (Calkin X) := by
        simpa only [Cardinal.lift_uzero] using
          e.toContinuousLinearEquiv.toEquiv.symm.lift_cardinal_eq
  have hsmall := mk_calkin_le_two_power_continuum X hX
  have hstrict : 2 ^ Cardinal.continuum < Cardinal.lift.{v} bethOmega.{0} := by
    have h : (2 : Cardinal.{0}) ^ Cardinal.continuum < bethOmega.{0} :=
      bethOmega_isStrongLimit.two_power_lt continuum_lt_bethOmega
    simpa only [Cardinal.lift_power, Cardinal.lift_two, Cardinal.lift_continuum] using
      (Cardinal.lift_lt.mpr h : Cardinal.lift.{v} ((2 : Cardinal.{0}) ^ Cardinal.continuum) <
        Cardinal.lift.{v} bethOmega.{0})
  exact not_le_of_gt hstrict (hlarge.trans hsmall)

theorem continuum_lt_mk_of_shiftQuotient_calkinIso
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)) :
    Cardinal.continuum < Cardinal.mk X :=
  continuum_lt_mk_of_large_calkinIso X bethOmega_le_mk_shiftQuotient e

end SurveyStatements.P2
