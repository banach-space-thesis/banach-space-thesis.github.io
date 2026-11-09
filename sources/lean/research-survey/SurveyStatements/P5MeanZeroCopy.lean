import SurveyStatements.P5HalfReflection

/-! Concrete complemented mean-zero copies for vector-valued interval Lp.
The bounds one and two suffice for the main theorem's existential uniform
constant. They are not claimed to be the sharper norm-one retraction stated
in the paper's signed-doubling lemma. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option profiler true
open MeasureTheory Set Filter
open scoped ENNReal

namespace SurveyStatements.P5
open SurveyStatements.P5Support
attribute [local irreducible] vectorLpBlockEquiv vectorLpAffine

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An antisymmetric half-copy, normalized to have norm at most one. -/
def meanZeroCopyInjection (hp : p ≠ ∞) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  ((1 / 2 : ℝ) : 𝕜) • (rightHalfInjection (𝕜 := 𝕜) hp -
    (reflectionLp (𝕜 := 𝕜)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (rightHalfInjection (𝕜 := 𝕜) hp))

def meanZeroCopyRetraction (hp : p ≠ ∞) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  (2 : 𝕜) • rightHalfRetraction (𝕜 := 𝕜) hp

theorem meanZeroCopy_retraction (hp : p ≠ ∞) :
    (meanZeroCopyRetraction (𝕜 := 𝕜) (E := E) hp).comp (meanZeroCopyInjection (𝕜 := 𝕜) hp) =
      ContinuousLinearMap.id 𝕜 (Lp E p unitIntervalMeasure) := by
  apply ContinuousLinearMap.ext
  intro f
  change (2 : 𝕜) • rightHalfRetraction (𝕜 := 𝕜) hp
    (((1 / 2 : ℝ) : 𝕜) • (rightHalfInjection (𝕜 := 𝕜) hp f -
      reflectionLp (𝕜 := 𝕜) (rightHalfInjection (𝕜 := 𝕜) hp f))) = f
  rw [map_smul, map_sub, rightHalfRetraction_injection, rightHalfRetraction_reflectedInjection,
    sub_zero, smul_smul]
  have hscalar : (2 : 𝕜) * ((1 / 2 : ℝ) : 𝕜) = 1 := by
    rw [RCLike.ofReal_div, RCLike.ofReal_one, RCLike.ofReal_ofNat]
    norm_num
  rw [hscalar, one_smul]

theorem meanZeroCopyInjection_mean_zero (hp : p ≠ ∞) (f : Lp E p unitIntervalMeasure) :
    probabilityLpMean (𝕜 := 𝕜) (meanZeroCopyInjection (𝕜 := 𝕜) hp f) = 0 := by
  change probabilityLpMean (𝕜 := 𝕜) (((1 / 2 : ℝ) : 𝕜) •
    (rightHalfInjection (𝕜 := 𝕜) hp f - reflectionLp (𝕜 := 𝕜) (rightHalfInjection (𝕜 := 𝕜) hp f))) = 0
  rw [map_smul, antisymmetric_mean_zero, smul_zero]

theorem norm_meanZeroCopyInjection_le (hp : p ≠ ∞) :
    ‖meanZeroCopyInjection (𝕜 := 𝕜) (E := E) hp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖((1 / 2 : ℝ) : 𝕜) • (rightHalfInjection (𝕜 := 𝕜) hp f -
    reflectionLp (𝕜 := 𝕜) (rightHalfInjection (𝕜 := 𝕜) hp f))‖ ≤ 1 * ‖f‖
  rw [norm_smul, RCLike.norm_ofReal]
  have h := norm_sub_le (rightHalfInjection (𝕜 := 𝕜) hp f)
    (reflectionLp (𝕜 := 𝕜) (rightHalfInjection (𝕜 := 𝕜) hp f))
  rw [LinearIsometryEquiv.norm_map, norm_rightHalfInjection] at h
  norm_num
  linarith

theorem norm_meanZeroCopyRetraction_le (hp : p ≠ ∞) :
    ‖meanZeroCopyRetraction (𝕜 := 𝕜) (E := E) hp‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖(2 : 𝕜) • rightHalfRetraction (𝕜 := 𝕜) hp f‖ ≤ 2 * ‖f‖
  rw [norm_smul]
  have hn : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
  rw [hn]
  exact mul_le_mul_of_nonneg_left (norm_rightHalfRetraction_le hp f) (by norm_num)

end SurveyStatements.P5

