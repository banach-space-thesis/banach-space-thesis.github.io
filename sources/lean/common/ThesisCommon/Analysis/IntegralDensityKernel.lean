import ThesisCommon.Analysis.IntegralKernelSigmaFiniteBound
import Mathlib.Probability.Kernel.WithDensity

/-! A bounded measurable reverse kernel for an integral operator's absolute
density. Exceptional columns are replaced by zero using a measurable mass
test, giving a genuine finite kernel with a uniform bound everywhere. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (ν : Measure Y) [SFinite ν] (k : X × Y → 𝕜) (C : ℝ)

def rawIntegralDensityKernel : Kernel X Y :=
  (Kernel.const X ν).withDensity (fun x y => ENNReal.ofReal ‖k (x, y)‖)

theorem measurable_integralDensity_goodSet :
    MeasurableSet {x | rawIntegralDensityKernel ν k x univ ≤ ENNReal.ofReal C} :=
  measurableSet_le (Kernel.measurable_coe _ MeasurableSet.univ) measurable_const

def boundedIntegralDensityKernel : Kernel X Y :=
  Kernel.piecewise (measurable_integralDensity_goodSet ν k C) (rawIntegralDensityKernel ν k) 0

theorem boundedIntegralDensityKernel_mass_le (x : X) :
    boundedIntegralDensityKernel ν k C x univ ≤ ENNReal.ofReal C := by
  rw [boundedIntegralDensityKernel, Kernel.piecewise_apply']
  split_ifs with hx
  · exact hx
  · simp

instance boundedIntegralDensityKernel_finite : IsFiniteKernel (boundedIntegralDensityKernel ν k C) :=
  ⟨⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, boundedIntegralDensityKernel_mass_le ν k C⟩⟩

theorem rawIntegralDensityKernel_apply (hk : Measurable k) (x : X) :
    rawIntegralDensityKernel ν k x = ν.withDensity (fun y => ENNReal.ofReal ‖k (x, y)‖) := by
  rw [rawIntegralDensityKernel, Kernel.withDensity_apply _ hk.norm.ennreal_ofReal, Kernel.const_apply]

variable {ν k C} {μ : Measure X}

theorem HasKernelBound.ae_integralDensity_goodSet (hk : Measurable k)
    (hb : HasKernelBound μ ν k C) :
    ∀ᵐ x ∂μ, rawIntegralDensityKernel ν k x univ ≤ ENNReal.ofReal C := by
  filter_upwards [hb] with x hx
  rw [rawIntegralDensityKernel_apply ν k hk, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal hx.1.norm
      (Eventually.of_forall fun y => norm_nonneg (k (x, y)))]
  exact ENNReal.ofReal_le_ofReal hx.2

theorem HasKernelBound.boundedIntegralDensityKernel_apply_ae (hk : Measurable k)
    (hb : HasKernelBound μ ν k C) :
    ∀ᵐ x ∂μ, boundedIntegralDensityKernel ν k C x =
      ν.withDensity (fun y => ENNReal.ofReal ‖k (x, y)‖) := by
  filter_upwards [hb.ae_integralDensity_goodSet hk] with x hx
  rw [boundedIntegralDensityKernel, Kernel.piecewise_apply,
    if_pos (show x ∈ {a | rawIntegralDensityKernel ν k a univ ≤ ENNReal.ofReal C} from hx),
    rawIntegralDensityKernel_apply ν k hk]

theorem HasKernelBound.boundedIntegralDensityKernel_real_ae (hk : Measurable k)
    (hb : HasKernelBound μ ν k C) :
    ∀ᵐ x ∂μ, ∀ B : Set Y, MeasurableSet B →
      (boundedIntegralDensityKernel ν k C x).real B = ∫ y in B, ‖k (x, y)‖ ∂ν := by
  filter_upwards [hb, hb.boundedIntegralDensityKernel_apply_ae hk] with x hx hκ
  intro B hB
  rw [measureReal_def, hκ, withDensity_apply _ hB,
    ← ofReal_integral_eq_lintegral_ofReal hx.1.norm.integrableOn
      (Eventually.of_forall fun y => norm_nonneg (k (x, y))),
    ENNReal.toReal_ofReal (integral_nonneg fun y => norm_nonneg (k (x, y)))]

end ThesisCommon
