import ThesisCommon.Analysis.ContinuousMapRieszVariation
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Uniqueness and additivity of the signed Riesz representation.
The approximation hypothesis is automatic for metrizable spaces, including the interval. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]

theorem finite_signed_representation_unique (P N Q R : Measure K)
    [IsFiniteMeasure P] [IsFiniteMeasure N] [IsFiniteMeasure Q] [IsFiniteMeasure R]
    (h : ∀ f : C(K, ℝ), (∫ t, f t ∂P) - ∫ t, f t ∂N =
      (∫ t, f t ∂Q) - ∫ t, f t ∂R) :
    P.toSignedMeasure - N.toSignedMeasure = Q.toSignedMeasure - R.toSignedMeasure := by
  have hm : P + R = Q + N := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hf := h f.toContinuousMap
    change (∫ t, f.toContinuousMap t ∂(P + R)) = ∫ t, f.toContinuousMap t ∂(Q + N)
    rw [integral_add_measure (continuousMap_integrable_finite P f.toContinuousMap)
        (continuousMap_integrable_finite R f.toContinuousMap),
      integral_add_measure (continuousMap_integrable_finite Q f.toContinuousMap)
        (continuousMap_integrable_finite N f.toContinuousMap)]
    linarith
  have hs := Measure.toSignedMeasure_eq_toSignedMeasure_iff.mpr hm
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at hs
  exact sub_eq_sub_iff_add_eq_add.mpr hs

theorem continuousMapRieszSigned_unique (μ : C(K, ℝ) →L[ℝ] ℝ)
    (P N : Measure K) [IsFiniteMeasure P] [IsFiniteMeasure N]
    (h : ∀ f : C(K, ℝ), μ f = (∫ t, f t ∂P) - ∫ t, f t ∂N) :
    continuousMapRieszSigned μ = P.toSignedMeasure - N.toSignedMeasure :=
  finite_signed_representation_unique _ _ _ _
    (fun f => (continuousMap_real_riesz_representation μ f).symm.trans (h f))

theorem continuousMapRieszSigned_add (μ ν : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapRieszSigned (μ + ν) = continuousMapRieszSigned μ + continuousMapRieszSigned ν := by
  have h := continuousMapRieszSigned_unique (μ + ν)
    (continuousMapRieszPositive μ + continuousMapRieszPositive ν)
    (continuousMapRieszNegative μ + continuousMapRieszNegative ν) (fun f => by
      rw [integral_add_measure (continuousMap_integrable_finite _ f)
          (continuousMap_integrable_finite _ f),
        integral_add_measure (continuousMap_integrable_finite _ f)
          (continuousMap_integrable_finite _ f),
        ContinuousLinearMap.add_apply,
        continuousMap_real_riesz_representation μ f,
        continuousMap_real_riesz_representation ν f]
      ring)
  rw [h, Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
  simp only [continuousMapRieszSigned]
  abel

theorem continuousMapRieszSigned_zero : continuousMapRieszSigned (0 : C(K, ℝ) →L[ℝ] ℝ) = 0 := by
  simpa using continuousMapRieszSigned_unique (0 : C(K, ℝ) →L[ℝ] ℝ) 0 0 (by simp)

theorem continuousMapRieszSigned_neg (μ : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapRieszSigned (-μ) = -continuousMapRieszSigned μ := by
  have h := continuousMapRieszSigned_add μ (-μ)
  rw [add_neg_cancel, continuousMapRieszSigned_zero] at h
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  exact h.symm

theorem continuousMapRieszSigned_sub (μ ν : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapRieszSigned (μ - ν) = continuousMapRieszSigned μ - continuousMapRieszSigned ν := by
  rw [sub_eq_add_neg, continuousMapRieszSigned_add, continuousMapRieszSigned_neg, sub_eq_add_neg]

end ThesisCommon
