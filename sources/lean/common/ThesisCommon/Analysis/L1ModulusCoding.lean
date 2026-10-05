import ThesisCommon.Analysis.OperatorModulusTransport
import ThesisCommon.Analysis.L1OperatorModulus
import ThesisCommon.Analysis.IntegralKernelCoding

/-! Modulus preservation by the actual coding isometries used in PEMS.
Singular-band preservation additionally needs the integral band theorem. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y A B : Type*}
variable [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable [mA : MeasurableSpace A] [mB : MeasurableSpace B]

theorem lOneOperatorModulus_lpTransport (μ : Measure X) (ν : Measure Y)
    (a : X → A) (ha : Measurable a) (hagen : mA.comap a = mX)
    (b : Y → B) (hb : Measurable b) (hbgen : mB.comap b = mY)
    (T : Lp ℝ 1 (μ.map a) →L[ℝ] Lp ℝ 1 (ν.map b)) :
    lOneOperatorModulus (lpTransportOperator μ ν a ha hagen b hb hbgen T) =
      lpTransportOperator μ ν a ha hagen b hb hbgen (lOneOperatorModulus T) :=
  operatorModulus_operatorTransport
    (lOne_norm_add_of_nonneg (μ.map a)) (lOne_norm_add_of_nonneg (ν.map b))
    (lOne_norm_add_of_nonneg μ) (lOne_norm_add_of_nonneg ν)
    (lpComapEquiv μ a ha hagen 1) (lpComapEquiv ν b hb hbgen 1)
    (lpComapEquiv_le_iff μ a ha hagen 1) (lpComapEquiv_le_iff ν b hb hbgen 1) T

end ThesisCommon
