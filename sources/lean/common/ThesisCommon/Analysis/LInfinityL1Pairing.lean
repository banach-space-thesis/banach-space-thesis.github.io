import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul
import ThesisCommon.Analysis.L1IndicatorExt
import ThesisCommon.Residuum

/-! The actual real L-infinity/L1 integral pairing, with its norm bound and
indicator tests. No dual representation theorem is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def linftyL1Pairing (μ : Measure X) : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 1 μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1

theorem linftyL1Pairing_apply (g : Lp ℝ ∞ μ) (f : Lp ℝ 1 μ) :
    linftyL1Pairing μ g f = ∫ x, g x * f x ∂μ := by
  exact (ContinuousLinearMap.mul ℝ ℝ).lpPairing_eq_integral g f

theorem linftyL1Pairing_bound (g : Lp ℝ ∞ μ) (f : Lp ℝ 1 μ) :
    ‖linftyL1Pairing μ g f‖ ≤ ‖g‖ * ‖f‖ := by
  rw [linftyL1Pairing_apply]
  have heq : (∫ x, g x * f x ∂μ) =
      L1.integral ((ContinuousLinearMap.mul ℝ ℝ).holder 1 g f) := by
    rw [L1.integral_eq_integral]
    exact (integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder g f)).symm
  rw [heq]
  calc
    _ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ).holder 1 g f‖ := L1.norm_integral_le _
    _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖g‖ * ‖f‖ :=
      (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le g f
    _ ≤ 1 * ‖g‖ * ‖f‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = _ := by rw [one_mul]

theorem norm_linftyL1Pairing_le (g : Lp ℝ ∞ μ) : ‖linftyL1Pairing μ g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (linftyL1Pairing_bound g)

theorem linfty_ae_norm_le_norm (g : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖g‖ := by
  filter_upwards [enorm_ae_le_eLpNormEssSup g μ] with x hx
  have ht : eLpNormEssSup g μ ≠ ∞ := by simpa only [eLpNorm_exponent_top] using (Lp.memLp g).2.ne
  have hh := ENNReal.toReal_mono ht hx
  simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, Lp.norm_def,
    eLpNorm_exponent_top] using hh

theorem linfty_norm_le_of_ae_bound (g : Lp ℝ ∞ μ) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) : ‖g‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hg)).trans_eq
    (ENNReal.toReal_ofReal hC)

theorem linftyL1Pairing_indicator [IsFiniteMeasure μ]
    (g : Lp ℝ ∞ μ) (A : Set X) (hA : MeasurableSet A) :
    linftyL1Pairing μ g (lOneIndicator μ A hA) = ∫ x in A, g x ∂μ := by
  rw [linftyL1Pairing_apply, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [lOneIndicator_coe (μ := μ) A hA] with x hx
  rw [hx]
  by_cases hxA : x ∈ A <;> simp [hxA]

theorem linftyL1Pairing_injective [IsFiniteMeasure μ] :
    Function.Injective (linftyL1Pairing μ) := by
  intro g h heq
  apply Lp.ext
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => ((Lp.memLp g).integrable le_top).integrableOn)
    (fun _ _ _ => ((Lp.memLp h).integrable le_top).integrableOn)
  intro A hA _
  simpa only [linftyL1Pairing_indicator] using
    congrArg (fun φ : Lp ℝ 1 μ →L[ℝ] ℝ => φ (lOneIndicator μ A hA)) heq

def linftyOne (μ : Measure X) : Lp ℝ ∞ μ :=
  (memLp_top_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))

theorem linftyOne_coe : linftyOne μ =ᵐ[μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _

theorem linftyL1Pairing_one : linftyL1Pairing μ (linftyOne μ) =
    (L1.integralCLM : Lp ℝ 1 μ →L[ℝ] ℝ) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [linftyL1Pairing_apply, ← L1.integral_def, L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [linftyOne_coe (μ := μ)] with x hx
  simp only [hx, one_mul]

end ThesisCommon
