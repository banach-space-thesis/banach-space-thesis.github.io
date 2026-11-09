import SurveyStatements.P5Averages
import SurveyStatements.P5SelfSimilarity

/-! The measure-preserving interval reflection used to construct actual
mean-zero complemented copies, with vector-valued Bochner functions. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace SurveyStatements.P5
open SurveyStatements.P5Support

def unitReflection : ℝ ≃ᵐ ℝ :=
  ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft (1 : ℝ))).toMeasurableEquiv

@[simp] theorem unitReflection_apply (x : ℝ) : unitReflection x = 1 - x := rfl

theorem unitReflection_volume : MeasurePreserving unitReflection volume volume := by
  have hneg : Measure.map (fun x : ℝ => -x) volume = volume := by
    simpa using Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)
  refine ⟨unitReflection.measurable, ?_⟩
  change Measure.map ((fun x : ℝ => 1 + x) ∘ (fun x : ℝ => -x)) volume = volume
  rw [← Measure.map_map (measurable_const_add 1) measurable_neg,
    hneg, map_add_left_eq_self]

theorem unitReflection_preimage : unitReflection ⁻¹' Icc (0 : ℝ) 1 = Icc 0 1 := by
  ext x
  change (0 ≤ 1 - x ∧ 1 - x ≤ 1) ↔ (0 ≤ x ∧ x ≤ 1)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem unitReflection_measure :
    MeasurePreserving unitReflection unitIntervalMeasure unitIntervalMeasure := by
  have h := unitReflection_volume.restrict_preimage (s := Icc (0 : ℝ) 1) measurableSet_Icc
  simpa only [unitReflection_preimage, unitIntervalMeasure] using h

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def reflectionLp : Lp E p unitIntervalMeasure ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure :=
  lebesgueLpTransport unitReflection unitReflection_measure

theorem reflectionLp_ae (f : Lp E p unitIntervalMeasure) :
    reflectionLp (𝕜 := 𝕜) f =ᵐ[unitIntervalMeasure] fun x => f (unitReflection x) :=
  Lp.coeFn_compMeasurePreserving f unitReflection_measure

theorem norm_reflectionLp_le :
    ‖(reflectionLp (𝕜 := 𝕜) (E := E) (p := p)).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖reflectionLp (𝕜 := 𝕜) f‖ ≤ 1 * ‖f‖
  rw [LinearIsometryEquiv.norm_map, one_mul]

variable [CompleteSpace E]
local instance : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
local instance : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

theorem reflectionLp_integral (f : Lp E p unitIntervalMeasure) :
    probabilityLpIntegral (𝕜 := 𝕜) (reflectionLp (𝕜 := 𝕜) f) =
      probabilityLpIntegral (𝕜 := 𝕜) f := by
  rw [probabilityLpIntegral_apply, probabilityLpIntegral_apply,
    integral_congr_ae (reflectionLp_ae f)]
  exact unitReflection_measure.integral_comp' f

theorem reflectionLp_mean (f : Lp E p unitIntervalMeasure) :
    probabilityLpMean (𝕜 := 𝕜) (reflectionLp (𝕜 := 𝕜) f) =
      probabilityLpMean (𝕜 := 𝕜) f := by
  rw [probabilityLpMean_apply, probabilityLpMean_apply, reflectionLp_integral]

theorem antisymmetric_mean_zero (f : Lp E p unitIntervalMeasure) :
    probabilityLpMean (𝕜 := 𝕜) (f - reflectionLp (𝕜 := 𝕜) f) = 0 := by
  rw [map_sub, reflectionLp_mean, sub_self]

end SurveyStatements.P5
