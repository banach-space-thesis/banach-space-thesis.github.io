import SurveyStatements.P5HalfCopy

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

theorem rightHalf_reflection_not_mem {x : ℝ} (hx : x ∈ intervalLpDyadicBlock 0) :
    unitReflection x ∉ intervalLpDyadicBlock 0 := by
  have hx' : 1 / 2 < x ∧ x ≤ 1 := by
    simpa [intervalLpDyadicBlock, intervalLpDyadicRadius] using hx
  simp only [intervalLpDyadicBlock, intervalLpDyadicRadius, zero_add, pow_one,
    pow_zero, mem_Ioc, unitReflection_apply]
  rintro ⟨h, _⟩
  linarith

theorem blockCopyRetraction_reflectedInjection
    (e : Lp E p (unitIntervalMeasure.restrict (intervalLpDyadicBlock 0))
      ≃ₗᵢ[𝕜] Lp E p unitIntervalMeasure)
    (f : Lp E p unitIntervalMeasure) :
    blockCopyRetraction (intervalLpDyadicBlock 0) e
      (reflectionLp (𝕜 := 𝕜) (blockCopyInjection (intervalLpDyadicBlock 0) measurableSet_Ioc e f)) = 0 := by
  have hzero : lebesgueLpRestrict (𝕜 := 𝕜) (intervalLpDyadicBlock 0)
      (reflectionLp (𝕜 := 𝕜) (blockCopyInjection (intervalLpDyadicBlock 0) measurableSet_Ioc e f)) = 0 := by
    apply Lp.ext
    have hsupport := lebesgueLpExtend_coe (𝕜 := 𝕜) (intervalLpDyadicBlock 0)
      measurableSet_Ioc (e.symm f)
    have hpull := unitReflection_measure.quasiMeasurePreserving.ae hsupport
    filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) (intervalLpDyadicBlock 0)
        (reflectionLp (𝕜 := 𝕜) (blockCopyInjection (intervalLpDyadicBlock 0) measurableSet_Ioc e f)),
      ae_restrict_of_ae (reflectionLp_ae (𝕜 := 𝕜) (blockCopyInjection (intervalLpDyadicBlock 0) measurableSet_Ioc e f)),
      ae_restrict_of_ae hpull, ae_restrict_mem (show MeasurableSet (intervalLpDyadicBlock 0)
        from measurableSet_Ioc), Lp.coeFn_zero E p
        (unitIntervalMeasure.restrict (intervalLpDyadicBlock 0))] with x hr href hs hx hz
    rw [hr, href, hz]
    change (lebesgueLpExtend (𝕜 := 𝕜) (intervalLpDyadicBlock 0) measurableSet_Ioc
      (e.symm f)) (unitReflection x) = 0
    rw [hs, Set.indicator_of_notMem (rightHalf_reflection_not_mem hx)]
  change e
    (lebesgueLpRestrict (𝕜 := 𝕜) (intervalLpDyadicBlock 0)
      (reflectionLp (𝕜 := 𝕜) (blockCopyInjection (intervalLpDyadicBlock 0) measurableSet_Ioc e f))) = 0
  rw [hzero, map_zero]

theorem rightHalfRetraction_reflectedInjection (hp : p ≠ ∞)
    (f : Lp E p unitIntervalMeasure) :
    rightHalfRetraction (𝕜 := 𝕜) hp
      (reflectionLp (𝕜 := 𝕜) (rightHalfInjection (𝕜 := 𝕜) hp f)) = 0 :=
  blockCopyRetraction_reflectedInjection (vectorLpBlockEquiv (𝕜 := 𝕜) hp 0) f

end SurveyStatements.P5

