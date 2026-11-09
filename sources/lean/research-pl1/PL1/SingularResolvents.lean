import PL1.ConcreteResolvents
import PL1.SingularCarrier
import PL1.SingularConvolution
import PL1.ScalarRealification

/-! # Singular averaged resolvents and the actual intrinsic RNP obstruction -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PL1.Noise

open Walsh Carrier ExponentialTime

theorem resolventMeasure_carrier (rates : ℕ → ℝ≥0) {t : ℝ} (ht : 0 < t)
    (N : Set Walsh.Group) (hN : MeasurableSet N)
    (hnoise : ∀ u : ℝ≥0, measure rates u N = 1) : resolventMeasure rates t N = 1 := by
  let := isProbabilityMeasure_timeMeasure ht
  rw [resolventMeasure, Measure.bind_apply hN (kernel rates).aemeasurable]
  simp only [kernel_apply, hnoise, lintegral_one, measure_univ]

theorem schur_resolvent_commonSet (t : PositiveTime) (d : ℕ) :
    resolventMeasure schurRates t (commonSet d) = 1 :=
  resolventMeasure_carrier schurRates t.property (commonSet d) (measurableSet_commonSet d)
    (fun u => noise_commonSet_eq_one u d)

theorem constant_resolvent_commonSet (t : PositiveTime) (d : ℕ) :
    resolventMeasure constantRates t (commonSet d) = 1 :=
  resolventMeasure_carrier constantRates t.property (commonSet d) (measurableSet_commonSet d)
    (fun u => noise_constantRates_commonSet_eq_one u d)

theorem schur_resolvent_singular (t : PositiveTime) :
    resolventMeasure schurRates t ⟂ₘ haar := by
  let := isProbabilityMeasure_resolventMeasure schurRates t.property
  refine ⟨(commonSet 0)ᶜ, (measurableSet_commonSet 0).compl, ?_, ?_⟩
  · rw [measure_compl (measurableSet_commonSet 0) (measure_ne_top _ _),
      measure_univ, schur_resolvent_commonSet, tsub_self]
  · simpa only [compl_compl] using haar_commonSet_eq_zero 0

theorem constant_resolvent_singular (t : PositiveTime) :
    resolventMeasure constantRates t ⟂ₘ haar := by
  let := isProbabilityMeasure_resolventMeasure constantRates t.property
  refine ⟨(commonSet 0)ᶜ, (measurableSet_commonSet 0).compl, ?_, ?_⟩
  · rw [measure_compl (measurableSet_commonSet 0) (measure_ne_top _ _),
      measure_univ, constant_resolvent_commonSet, tsub_self]
  · simpa only [compl_compl] using haar_commonSet_eq_zero 0

/-- A charged Haar-null carrier of the zeroth resolvent forces failure of the
full reviewed vector-measure RNP in the actual real intrinsic Banach space. -/
theorem intrinsic_not_RNP_of_resolvent_carrier (rates : ℕ → ℝ≥0)
    (N : Set Walsh.Group) (hmN : haar N = 0)
    (hνN : resolventMeasure rates (dyadicTime 0) N ≠ 0) :
    ¬ HasRadonNikodymProperty.{_, 0} (dyadicSystem ℝ rates).IntrinsicSpace := by
  let := isProbabilityMeasure_resolventMeasure rates (dyadicTime 0).property
  apply SingularConvolution.not_RNP_of_convolution_factorization
    (resolventMeasure rates (dyadicTime 0)) N hmN hνN
    ((dyadicSystem ℝ rates).column 0)
    (IntrinsicGraph.evalZero (dyadicSystem ℝ rates).analysis)
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply, DyadicSystem.evalZero_column]
  rfl

theorem schur_intrinsic_not_RNP_real :
    ¬ HasRadonNikodymProperty.{_, 0} (dyadicSystem ℝ schurRates).IntrinsicSpace :=
  intrinsic_not_RNP_of_resolvent_carrier schurRates (commonSet 0)
    (haar_commonSet_eq_zero 0) (by rw [schur_resolvent_commonSet]; exact one_ne_zero)

theorem constant_intrinsic_not_RNP_real :
    ¬ HasRadonNikodymProperty.{_, 0} (dyadicSystem ℝ constantRates).IntrinsicSpace :=
  intrinsic_not_RNP_of_resolvent_carrier constantRates (commonSet 0)
    (haar_commonSet_eq_zero 0) (by rw [constant_resolvent_commonSet]; exact one_ne_zero)

theorem schur_projection_range_not_RNP_real :
    ¬ HasRadonNikodymProperty.{_, 0} (projection ℝ schurRates).range := by
  change ¬ HasRadonNikodymProperty.{_, 0} (dyadicSystem ℝ schurRates).projection.range
  rw [DyadicSystem.projection_range]
  exact schur_intrinsic_not_RNP_real

theorem constant_projection_range_not_RNP_real :
    ¬ HasRadonNikodymProperty.{_, 0} (projection ℝ constantRates).range := by
  change ¬ HasRadonNikodymProperty.{_, 0} (dyadicSystem ℝ constantRates).projection.range
  rw [DyadicSystem.projection_range]
  exact constant_intrinsic_not_RNP_real

/-- The same obstruction holds for the underlying real space of the scalar
construction, with exactly its inherited norm. -/
theorem intrinsic_not_RNP_of_resolvent_carrier_scalar (𝕜 : Type*) [RCLike 𝕜]
    (rates : ℕ → ℝ≥0) (N : Set Walsh.Group) (hmN : haar N = 0)
    (hνN : resolventMeasure rates (dyadicTime 0) N ≠ 0) :
    ¬ @HasRadonNikodymProperty.{_, 0}
      (UnderlyingReal 𝕜 (dyadicSystem 𝕜 rates).IntrinsicSpace)
      (inferInstanceAs (NormedAddCommGroup (dyadicSystem 𝕜 rates).IntrinsicSpace))
      (NormedSpace.restrictScalars ℝ 𝕜 (dyadicSystem 𝕜 rates).IntrinsicSpace) := by
  let : NormedSpace ℝ (dyadicSystem 𝕜 rates).IntrinsicSpace :=
    NormedSpace.restrictScalars ℝ 𝕜 (dyadicSystem 𝕜 rates).IntrinsicSpace
  let := IsScalarTower.restrictScalars ℝ 𝕜 (dyadicSystem 𝕜 rates).IntrinsicSpace
  let := isProbabilityMeasure_resolventMeasure rates (dyadicTime 0).property
  apply ScalarRealification.not_RNP_of_scalar_convolution_factorization 𝕜
    (resolventMeasure rates (dyadicTime 0)) N hmN hνN
    ((dyadicSystem 𝕜 rates).column 0)
    (IntrinsicGraph.evalZero (dyadicSystem 𝕜 rates).analysis)
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply, DyadicSystem.evalZero_column]
  rfl

theorem schur_intrinsic_not_RNP (𝕜 : Type*) [RCLike 𝕜] :
    ¬ @HasRadonNikodymProperty.{_, 0}
      (UnderlyingReal 𝕜 (dyadicSystem 𝕜 schurRates).IntrinsicSpace)
      (inferInstanceAs (NormedAddCommGroup (dyadicSystem 𝕜 schurRates).IntrinsicSpace))
      (NormedSpace.restrictScalars ℝ 𝕜 (dyadicSystem 𝕜 schurRates).IntrinsicSpace) :=
  intrinsic_not_RNP_of_resolvent_carrier_scalar 𝕜 schurRates (commonSet 0)
    (haar_commonSet_eq_zero 0) (by rw [schur_resolvent_commonSet]; exact one_ne_zero)

theorem constant_intrinsic_not_RNP (𝕜 : Type*) [RCLike 𝕜] :
    ¬ @HasRadonNikodymProperty.{_, 0}
      (UnderlyingReal 𝕜 (dyadicSystem 𝕜 constantRates).IntrinsicSpace)
      (inferInstanceAs (NormedAddCommGroup (dyadicSystem 𝕜 constantRates).IntrinsicSpace))
      (NormedSpace.restrictScalars ℝ 𝕜 (dyadicSystem 𝕜 constantRates).IntrinsicSpace) :=
  intrinsic_not_RNP_of_resolvent_carrier_scalar 𝕜 constantRates (commonSet 0)
    (haar_commonSet_eq_zero 0) (by rw [constant_resolvent_commonSet]; exact one_ne_zero)

theorem schur_projection_range_not_RNP (𝕜 : Type*) [RCLike 𝕜] :
    ¬ @HasRadonNikodymProperty.{_, 0} (UnderlyingReal 𝕜 (projection 𝕜 schurRates).range)
      (inferInstanceAs (NormedAddCommGroup (projection 𝕜 schurRates).range))
      (NormedSpace.restrictScalars ℝ 𝕜 (projection 𝕜 schurRates).range) := by
  change ¬ @HasRadonNikodymProperty.{_, 0}
    ((dyadicSystem 𝕜 schurRates).projection.range)
    (inferInstanceAs (NormedAddCommGroup (dyadicSystem 𝕜 schurRates).projection.range))
    (NormedSpace.restrictScalars ℝ 𝕜 (dyadicSystem 𝕜 schurRates).projection.range)
  rw [DyadicSystem.projection_range]
  exact schur_intrinsic_not_RNP 𝕜

theorem constant_projection_range_not_RNP (𝕜 : Type*) [RCLike 𝕜] :
    ¬ @HasRadonNikodymProperty.{_, 0} (UnderlyingReal 𝕜 (projection 𝕜 constantRates).range)
      (inferInstanceAs (NormedAddCommGroup (projection 𝕜 constantRates).range))
      (NormedSpace.restrictScalars ℝ 𝕜 (projection 𝕜 constantRates).range) := by
  change ¬ @HasRadonNikodymProperty.{_, 0}
    ((dyadicSystem 𝕜 constantRates).projection.range)
    (inferInstanceAs (NormedAddCommGroup (dyadicSystem 𝕜 constantRates).projection.range))
    (NormedSpace.restrictScalars ℝ 𝕜 (dyadicSystem 𝕜 constantRates).projection.range)
  rw [DyadicSystem.projection_range]
  exact constant_intrinsic_not_RNP 𝕜

end PL1.Noise
