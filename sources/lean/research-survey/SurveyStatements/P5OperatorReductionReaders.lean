import SurveyStatements.P5VectorBoundedMultiplication
import SurveyStatements.P5Tensors

/-! Actual bounded weighted outer integration over RCLike scalars, with
arbitrary Banach-valued outputs. These readers apply to every mixed input,
not just elementary tensors. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
local instance : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance : Module ℝ F := RestrictScalars.module ℝ 𝕜 F
local instance : IsScalarTower ℝ 𝕜 F := RestrictScalars.isScalarTower ℝ 𝕜 F
local instance : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F

def weightedOuterReader (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : Lp E p unitIntervalMeasure →L[𝕜] E :=
  (probabilityLpIntegral (𝕜 := 𝕜)).comp (vectorBoundedMultiply η hη hb)

theorem norm_weightedOuterReader_le (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : ‖weightedOuterReader (E := E) (p := p) η hη hb‖ ≤ 1 := by
  calc
    _ ≤ ‖probabilityLpIntegral (𝕜 := 𝕜) (E := E) (p := p)
        (μ := unitIntervalMeasure)‖ * ‖vectorBoundedMultiply (E := E) (p := p) η hη hb‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul norm_probabilityLpIntegral_le
      (norm_vectorBoundedMultiply_le η hη hb) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem weightedOuterReader_natural (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (L : E →L[𝕜] F) (f : Lp E p unitIntervalMeasure) :
    weightedOuterReader η hη hb (L.compLpL p unitIntervalMeasure f) =
      L (weightedOuterReader η hη hb f) := by
  have hmul : vectorBoundedMultiply η hη hb (L.compLpL p unitIntervalMeasure f) =
      L.compLpL p unitIntervalMeasure (vectorBoundedMultiply η hη hb f) := by
    apply Lp.ext
    filter_upwards [vectorBoundedMultiplyValue_ae η hη hb (L.compLpL p unitIntervalMeasure f),
      L.coeFn_compLpL f,
      L.coeFn_compLpL (vectorBoundedMultiply η hη hb f),
      vectorBoundedMultiplyValue_ae η hη hb f] with x h₁ h₂ h₃ h₄
    change (vectorBoundedMultiply η hη hb (L.compLpL p unitIntervalMeasure f)) x =
      η x • (L.compLpL p unitIntervalMeasure f) x at h₁
    change (vectorBoundedMultiply η hη hb f) x = η x • f x at h₄
    change (vectorBoundedMultiply η hη hb (L.compLpL p unitIntervalMeasure f)) x =
      (L.compLpL p unitIntervalMeasure (vectorBoundedMultiply η hη hb f)) x
    rw [h₁, h₂, h₃, h₄, map_smul]
  change probabilityLpIntegral (𝕜 := 𝕜)
      (vectorBoundedMultiply η hη hb (L.compLpL p unitIntervalMeasure f)) =
    L (probabilityLpIntegral (𝕜 := 𝕜) (vectorBoundedMultiply η hη hb f))
  rw [hmul, probabilityLpIntegral_apply, probabilityLpIntegral_apply,
    integral_congr_ae (L.coeFn_compLpL (vectorBoundedMultiply η hη hb f))]
  exact L.integral_comp_comm ((Lp.memLp (vectorBoundedMultiply η hη hb f)).integrable Fact.out)

theorem weightedOuterReader_tensor (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    weightedOuterReader η hη hb (tensorWith g f) =
      weightedOuterReader η hη hb f • g := by
  exact weightedOuterReader_natural η hη hb ((ContinuousLinearMap.id 𝕜 𝕜).smulRight g) f

end SurveyStatements.P5OperatorReduction
