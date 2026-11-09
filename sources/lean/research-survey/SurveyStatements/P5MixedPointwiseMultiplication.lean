import SurveyStatements.P5VectorBoundedMultiplication
import SurveyStatements.P5Tensors

/-! Actual contractive multiplication in either variable of the mixed Bochner
space. The tensor identities are used when localizing multiplier arguments. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def mixedOuterMultiply (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  vectorBoundedMultiply η hη hb

def mixedInnerMultiply (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (vectorBoundedMultiply (E := 𝕜) (p := 1) η hη hb).compLpL p unitIntervalMeasure

theorem norm_mixedOuterMultiply_le (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : ‖mixedOuterMultiply (p := p) η hη hb‖ ≤ 1 :=
  norm_vectorBoundedMultiply_le η hη hb

theorem norm_mixedInnerMultiply_le (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) : ‖mixedInnerMultiply (p := p) η hη hb‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans (norm_vectorBoundedMultiply_le η hη hb)

theorem mixedInnerMap_tensor (L : Lp 𝕜 1 unitIntervalMeasure →L[𝕜]
    Lp 𝕜 1 unitIntervalMeasure) (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    L.compLpL p unitIntervalMeasure (tensorWith g f) = tensorWith (L g) f := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (tensorWith g f), tensorWith_ae g f,
    tensorWith_ae (L g) f] with x hL hg hf
  rw [hL, hg, hf, map_smul]

theorem mixedInnerMultiply_tensor (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    mixedInnerMultiply η hη hb (tensorWith g f) =
      tensorWith (vectorBoundedMultiply η hη hb g) f :=
  mixedInnerMap_tensor _ _ _

theorem mixedOuterMultiply_tensor (η : ℝ → 𝕜) (hη : StronglyMeasurable η)
    (hb : ∀ x, ‖η x‖ ≤ 1) (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    mixedOuterMultiply η hη hb (tensorWith g f) =
      tensorWith g (vectorBoundedMultiply η hη hb f) := by
  apply Lp.ext
  filter_upwards [vectorBoundedMultiplyValue_ae η hη hb (tensorWith g f),
    tensorWith_ae g f, tensorWith_ae g (vectorBoundedMultiply η hη hb f),
    vectorBoundedMultiplyValue_ae η hη hb f] with x hM hg hf hηf
  change (mixedOuterMultiply η hη hb (tensorWith g f)) x = _ at hM
  change (vectorBoundedMultiply η hη hb f) x = _ at hηf
  rw [hM, hg, hf, hηf, smul_smul]
  rw [smul_eq_mul]

theorem mixedOuterMultiply_innerMap_commute (η : ℝ → 𝕜)
    (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (L : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure) :
    (mixedOuterMultiply (p := p) η hη hb).comp (L.compLpL p unitIntervalMeasure) =
      (L.compLpL p unitIntervalMeasure).comp (mixedOuterMultiply η hη hb) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [vectorBoundedMultiplyValue_ae η hη hb
      (L.compLpL p unitIntervalMeasure f),
    L.coeFn_compLpL f, L.coeFn_compLpL (mixedOuterMultiply η hη hb f),
    vectorBoundedMultiplyValue_ae η hη hb f] with x hM hL hLM hMf
  change (mixedOuterMultiply η hη hb (L.compLpL p unitIntervalMeasure f)) x = _ at hM
  change (mixedOuterMultiply η hη hb f) x = _ at hMf
  change (mixedOuterMultiply η hη hb (L.compLpL p unitIntervalMeasure f)) x =
    (L.compLpL p unitIntervalMeasure (mixedOuterMultiply η hη hb f)) x
  rw [hM, hL, hLM, hMf, map_smul]

end SurveyStatements.P5
