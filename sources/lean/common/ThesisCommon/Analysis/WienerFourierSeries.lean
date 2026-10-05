import ThesisCommon.Analysis.WienerCharacters
import ThesisCommon.Analysis.LpOneColumnsOperator
import Mathlib.Analysis.Fourier.AddCircle

/-! The actual uniformly convergent Fourier series of an absolutely
summable sequence. Coefficient recovery is obtained from the orthonormal
Fourier basis on the circle; it establishes injectivity without assuming
any operator quotient representation. -/
noncomputable section
open scoped ENNReal
open MeasureTheory
namespace ThesisCommon

def wienerFourierSeries : WienerSequences ℂ →L[ℂ] C(AddCircle (1 : ℝ), ℂ) :=
  lpOneColumnsOperator (fourier (T := 1)) 1 zero_le_one
    (fun n => (fourier_norm n).le)

theorem wienerFourierSeries_apply (a : WienerSequences ℂ) :
    wienerFourierSeries a = ∑' n : ℤ, a n • fourier (T := 1) n := rfl

theorem wienerFourierSeries_summable_norm (a : WienerSequences ℂ) :
    Summable (fun n : ℤ => ‖a n • fourier (T := 1) n‖) := by
  simpa only [norm_smul, fourier_norm, mul_one] using wiener_summable_norm a

theorem norm_wienerFourierSeries_le : ‖wienerFourierSeries‖ ≤ 1 :=
  norm_lpOneColumnsOperator_le _ _ _ _

@[simp] theorem wienerFourierSeries_single (n : ℤ) :
    wienerFourierSeries (lp.single 1 n 1) = fourier (T := 1) n := by
  rw [wienerFourierSeries_apply, tsum_eq_single n]
  · simp
  · intro k hk
    simp [lp.single_apply, hk]
    exact zero_smul ℂ (fourier (T := 1) k)

def wienerFourierCoefficient (n : ℤ) : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (fourierBasis (T := 1) n)).comp
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)

theorem wienerFourierCoefficient_eq (n : ℤ) (f : C(AddCircle (1 : ℝ), ℂ)) :
    wienerFourierCoefficient n f = fourierCoeff f n := by
  change inner ℂ (fourierBasis (T := 1) n)
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f) = _
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_toLp]

@[simp] theorem wienerFourierCoefficient_fourier (n k : ℤ) :
    wienerFourierCoefficient n (fourier (T := 1) k) = if n = k then 1 else 0 := by
  change inner ℂ (fourierBasis (T := 1) n) (fourierLp (T := 1) 2 k) = _
  rw [← coe_fourierBasis]
  exact orthonormal_iff_ite.mp fourierBasis.orthonormal n k

@[simp] theorem wienerFourierCoefficient_series (a : WienerSequences ℂ) (n : ℤ) :
    wienerFourierCoefficient n (wienerFourierSeries a) = a n := by
  rw [wienerFourierSeries_apply,
    (wienerFourierCoefficient n).map_tsum (wienerFourierSeries_summable_norm a).of_norm,
    tsum_eq_single n]
  · simp
  · intro k hk
    simp [Ne.symm hk]

theorem wienerFourierSeries_injective : Function.Injective wienerFourierSeries := by
  intro a b h
  apply lp.ext
  funext n
  have hh := congrArg (wienerFourierCoefficient n) h
  simpa only [wienerFourierCoefficient_series] using hh

theorem fourier_eq_toCircle_zpow (n : ℤ) (z : AddCircle (1 : ℝ)) :
    fourier n z = (AddCircle.toCircle z : ℂ)^n := by
  let h : AddCircle (1 : ℝ) →+ Additive Circle :=
    { toFun := fun x => Additive.ofMul (AddCircle.toCircle x)
      map_zero' := AddCircle.toCircle_zero
      map_add' := AddCircle.toCircle_add }
  have hh := h.map_zsmul z n
  have he : AddCircle.toCircle (n • z) = (AddCircle.toCircle z)^n := hh
  change (AddCircle.toCircle (n • z) : ℂ) = _
  rw [he]
  exact Metric.unitSphere.coe_zpow _ _

theorem wienerFourierSeries_evaluate (a : WienerSequences ℂ) (z : AddCircle (1 : ℝ)) :
    wienerFourierSeries a z = wienerEvaluate (AddCircle.toCircle z) a := by
  rw [wienerFourierSeries_apply, wienerEvaluate_apply]
  change (ContinuousMap.evalCLM ℂ z) (∑' n : ℤ, a n • fourier (T := 1) n) = _
  rw [(ContinuousMap.evalCLM ℂ z).map_tsum (wienerFourierSeries_summable_norm a).of_norm]
  apply tsum_congr
  intro n
  change a n * fourier n z = _
  rw [fourier_eq_toCircle_zpow]

theorem wienerFourierSeries_convolution (a b : WienerSequences ℂ) :
    wienerFourierSeries (wienerConvolution a b) =
      wienerFourierSeries a * wienerFourierSeries b := by
  ext z
  simp only [ContinuousMap.mul_apply, wienerFourierSeries_evaluate,
    wienerEvaluate_convolution]

end ThesisCommon
