import SurveyStatements.P5Reflection

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

theorem lift_retraction (L M : E →L[𝕜] E) (hLM : L.comp M = ContinuousLinearMap.id 𝕜 E) :
    (L.compLpL p unitIntervalMeasure).comp (M.compLpL p unitIntervalMeasure) =
      ContinuousLinearMap.id 𝕜 (Lp E p unitIntervalMeasure) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (M.compLpL p unitIntervalMeasure f), M.coeFn_compLpL f]
    with x houter hinner
  change (L.compLpL p unitIntervalMeasure (M.compLpL p unitIntervalMeasure f)) x = f x
  rw [houter, hinner]
  exact congrArg (fun A : E →L[𝕜] E => A (f x)) hLM

def blockCopyInjection (s : Set ℝ) (hs : MeasurableSet s)
    (e : Lp E p (unitIntervalMeasure.restrict s) ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  (lebesgueLpExtend (𝕜 := 𝕜) s hs).toContinuousLinearMap.comp
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap

def blockCopyRetraction (s : Set ℝ)
    (e : Lp E p (unitIntervalMeasure.restrict s) ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp (lebesgueLpRestrict (𝕜 := 𝕜) s)

theorem blockCopy_retraction (s : Set ℝ) (hs : MeasurableSet s)
    (e : Lp E p (unitIntervalMeasure.restrict s) ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure)
    (f : Lp E p unitIntervalMeasure) :
    blockCopyRetraction s e (blockCopyInjection s hs e f) = f := by
  change e (lebesgueLpRestrict (𝕜 := 𝕜) s (lebesgueLpExtend (𝕜 := 𝕜) s hs (e.symm f))) = f
  rw [lebesgueLpRestrict_extend, LinearIsometryEquiv.apply_symm_apply]

theorem norm_blockCopyInjection (s : Set ℝ) (hs : MeasurableSet s)
    (e : Lp E p (unitIntervalMeasure.restrict s) ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure)
    (f : Lp E p unitIntervalMeasure) : ‖blockCopyInjection s hs e f‖ = ‖f‖ := by
  change ‖lebesgueLpExtend (𝕜 := 𝕜) s hs (e.symm f)‖ = ‖f‖
  rw [LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]

theorem norm_blockCopyRetraction_le (s : Set ℝ)
    (e : Lp E p (unitIntervalMeasure.restrict s) ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure)
    (f : Lp E p unitIntervalMeasure) : ‖blockCopyRetraction s e f‖ ≤ ‖f‖ := by
  change ‖e (lebesgueLpRestrict (𝕜 := 𝕜) s f)‖ ≤ ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_restrict_le f p unitIntervalMeasure s)

def rightHalfInjection (hp : p ≠ ∞) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  blockCopyInjection (intervalLpDyadicBlock 0) measurableSet_Ioc (vectorLpBlockEquiv (𝕜 := 𝕜) hp 0)

def rightHalfRetraction (hp : p ≠ ∞) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  blockCopyRetraction (intervalLpDyadicBlock 0) (vectorLpBlockEquiv (𝕜 := 𝕜) hp 0)

theorem rightHalfRetraction_injection (hp : p ≠ ∞) (f : Lp E p unitIntervalMeasure) :
    rightHalfRetraction (𝕜 := 𝕜) hp (rightHalfInjection (𝕜 := 𝕜) hp f) = f :=
  blockCopy_retraction _ _ _ f

theorem norm_rightHalfInjection (hp : p ≠ ∞) (f : Lp E p unitIntervalMeasure) :
    ‖rightHalfInjection (𝕜 := 𝕜) hp f‖ = ‖f‖ := norm_blockCopyInjection _ _ _ f

theorem norm_rightHalfRetraction_le (hp : p ≠ ∞) (f : Lp E p unitIntervalMeasure) :
    ‖rightHalfRetraction (𝕜 := 𝕜) hp f‖ ≤ ‖f‖ := norm_blockCopyRetraction_le _ _ f

end SurveyStatements.P5

