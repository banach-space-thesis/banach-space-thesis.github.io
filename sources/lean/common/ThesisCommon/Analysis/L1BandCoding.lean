import ThesisCommon.Analysis.OperatorOrderTransport
import ThesisCommon.Analysis.L1ModulusCoding
import ThesisCommon.Analysis.IntegralOperatorBand

/-! Coding isometries preserve the genuine integral and singular classes,
and commute with the constructed integral-band projection. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y A B : Type*}
variable [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable [mA : MeasurableSpace A] [mB : MeasurableSpace B]
variable (μ : Measure X) (ν : Measure Y)
variable (a : X → A) (ha : Measurable a) (hagen : mA.comap a = mX)
variable (b : Y → B) (hb : Measurable b) (hbgen : mB.comap b = mY)

def lpTransportOperatorOrderIso :
    (Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) ≃o (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :=
  operatorTransportOrderIso (lpComapEquiv μ a ha hagen 1) (lpComapEquiv ν b hb hbgen 1)
    (lpComapEquiv_le_iff μ a ha hagen 1) (lpComapEquiv_le_iff ν b hb hbgen 1)

theorem lpTransportOperator_zero : lpTransportOperator (𝕜 := ℝ) μ ν a ha hagen b hb hbgen 0 = 0 :=
  operatorTransport_zero _ _

theorem lpTransportOperator_add (S T : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    lpTransportOperator μ ν a ha hagen b hb hbgen (S + T) =
      lpTransportOperator μ ν a ha hagen b hb hbgen S + lpTransportOperator μ ν a ha hagen b hb hbgen T :=
  operatorTransport_add _ _ S T

theorem lpTransportOperator_inf (S T : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    lpTransportOperator μ ν a ha hagen b hb hbgen (S ⊓ T) =
      lpTransportOperator μ ν a ha hagen b hb hbgen S ⊓ lpTransportOperator μ ν a ha hagen b hb hbgen T :=
  (lpTransportOperatorOrderIso μ ν a ha hagen b hb hbgen).map_inf S T

theorem lpTransportOperator_abs (T : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    lpTransportOperator μ ν a ha hagen b hb hbgen |T| = |lpTransportOperator μ ν a ha hagen b hb hbgen T| := by
  rw [abs_lOneOperator_eq, abs_lOneOperator_eq]
  exact (lOneOperatorModulus_lpTransport μ ν a ha hagen b hb hbgen T).symm

theorem isSingularOperator_lpTransport_iff [SFinite (μ.map a)]
    (S : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    IsSingularOperator (lpTransportOperator μ ν a ha hagen b hb hbgen S) ↔ IsSingularOperator S := by
  let e := lpTransportOperatorOrderIso μ ν a ha hagen b hb hbgen
  have he0 : e 0 = 0 := lpTransportOperator_zero μ ν a ha hagen b hb hbgen
  have habs : ∀ T, e |T| = |e T| := lpTransportOperator_abs μ ν a ha hagen b hb hbgen
  have hinf : ∀ T U, e (|T| ⊓ |U|) = |e T| ⊓ |e U| := by
    intro T U
    rw [e.map_inf, habs, habs]
  constructor
  · intro hS K hK
    apply e.injective
    rw [hinf, he0]
    exact hS (e K) ((isIntegralOperator_lpTransport_iff μ ν a ha hagen b hb hbgen K).mpr hK)
  · intro hS K hK
    obtain ⟨H, rfl⟩ := e.surjective K
    change |e S| ⊓ |e H| = 0
    rw [← hinf, hS H ((isIntegralOperator_lpTransport_iff μ ν a ha hagen b hb hbgen H).mp hK), he0]

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem integralBandProjection_lpTransport
    (T : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    integralBandProjection (lpTransportOperator μ ν a ha hagen b hb hbgen T) =
      lpTransportOperator μ ν a ha hagen b hb hbgen (integralBandProjection T) := by
  let e := lpTransportOperatorOrderIso μ ν a ha hagen b hb hbgen
  have hI : IsIntegralOperator (e (integralBandProjection T)) :=
    (isIntegralOperator_lpTransport_iff μ ν a ha hagen b hb hbgen _).mpr (integralBandProjection_isIntegral T)
  have hS : IsSingularOperator (e (T - integralBandProjection T)) :=
    (isSingularOperator_lpTransport_iff μ ν a ha hagen b hb hbgen _).mpr
      (integralBandProjection_residual_singular T)
  have hdecomp : e T = e (integralBandProjection T) + e (T - integralBandProjection T) := by
    have hadd : ∀ U V, e (U + V) = e U + e V := lpTransportOperator_add μ ν a ha hagen b hb hbgen
    rw [← hadd]
    congr 1
    abel
  change integralBandProjection (e T) = e (integralBandProjection T)
  rw [hdecomp, map_add, integralBandProjection_eq_self hI,
    (integralBandProjection_eq_zero_iff _).mpr hS, add_zero]

end ThesisCommon
