import ThesisCommon.Analysis.ContinuousMapJordanNorm
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-! Real Riesz representation of arbitrary bounded functionals on C(K).
The measures are genuine finite regular Borel measures constructed by RMK.
Signed integration is expressed as the difference of the two ordinary integrals. -/
noncomputable section
open MeasureTheory CompactlySupported
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

def compactSupportPositiveLinear (Λ : C(K, ℝ) →ₚ[ℝ] ℝ) : C_c(K, ℝ) →ₚ[ℝ] ℝ where
  toFun f := Λ f.toContinuousMap
  map_add' f g := Λ.map_add _ _
  map_smul' c f := Λ.map_smul c f.toContinuousMap
  monotone' := fun _ _ h => Λ.monotone h

def continuousMapRieszMeasure (Λ : C(K, ℝ) →ₚ[ℝ] ℝ) : Measure K :=
  RealRMK.rieszMeasure (compactSupportPositiveLinear Λ)

instance continuousMapRieszMeasure_regular (Λ : C(K, ℝ) →ₚ[ℝ] ℝ) :
    (continuousMapRieszMeasure Λ).Regular := by
  unfold continuousMapRieszMeasure RealRMK.rieszMeasure
  infer_instance

theorem continuousMapRieszMeasure_univ_le (Λ : C(K, ℝ) →ₚ[ℝ] ℝ) :
    continuousMapRieszMeasure Λ Set.univ ≤ ENNReal.ofReal (Λ 1) := by
  exact RealRMK.rieszMeasure_le_of_eq_one (compactSupportPositiveLinear Λ)
    (f := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported (1 : C(K, ℝ)))
    (fun _ => zero_le_one) isCompact_univ (fun _ _ => rfl)

instance continuousMapRieszMeasure_finite (Λ : C(K, ℝ) →ₚ[ℝ] ℝ) :
    IsFiniteMeasure (continuousMapRieszMeasure Λ) :=
  ⟨lt_of_le_of_lt (continuousMapRieszMeasure_univ_le Λ) ENNReal.ofReal_lt_top⟩

theorem integral_continuousMapRieszMeasure (Λ : C(K, ℝ) →ₚ[ℝ] ℝ) (f : C(K, ℝ)) :
    ∫ t, f t ∂continuousMapRieszMeasure Λ = Λ f := by
  exact RealRMK.integral_rieszMeasure (compactSupportPositiveLinear Λ)
    (CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported f)

theorem continuousMapRieszMeasure_mass (Λ : C(K, ℝ) →ₚ[ℝ] ℝ) :
    (continuousMapRieszMeasure Λ).real Set.univ = Λ 1 := by
  simpa using integral_continuousMapRieszMeasure Λ (1 : C(K, ℝ))

def continuousMapRieszPositive (μ : C(K, ℝ) →L[ℝ] ℝ) : Measure K :=
  continuousMapRieszMeasure (continuousMapPositiveLinear μ)

def continuousMapRieszNegative (μ : C(K, ℝ) →L[ℝ] ℝ) : Measure K :=
  continuousMapRieszMeasure (continuousMapNegativeLinear μ)

instance continuousMapRieszPositive_finite (μ : C(K, ℝ) →L[ℝ] ℝ) :
    IsFiniteMeasure (continuousMapRieszPositive μ) := by
  unfold continuousMapRieszPositive
  infer_instance

instance continuousMapRieszNegative_finite (μ : C(K, ℝ) →L[ℝ] ℝ) :
    IsFiniteMeasure (continuousMapRieszNegative μ) := by
  unfold continuousMapRieszNegative
  infer_instance

instance continuousMapRieszPositive_regular (μ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRieszPositive μ).Regular := by
  unfold continuousMapRieszPositive
  infer_instance

instance continuousMapRieszNegative_regular (μ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRieszNegative μ).Regular := by
  unfold continuousMapRieszNegative
  infer_instance

theorem continuousMap_real_riesz_representation (μ : C(K, ℝ) →L[ℝ] ℝ)
    (f : C(K, ℝ)) : μ f =
      (∫ t, f t ∂continuousMapRieszPositive μ) -
      (∫ t, f t ∂continuousMapRieszNegative μ) := by
  rw [continuousMapRieszPositive, continuousMapRieszNegative,
    integral_continuousMapRieszMeasure, integral_continuousMapRieszMeasure]
  change μ f = continuousMapPositivePart μ f - (continuousMapPositivePart μ f - μ f)
  ring

theorem continuousMapRieszPositive_mass (μ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRieszPositive μ).real Set.univ = ‖continuousMapPositivePart μ‖ := by
  rw [continuousMapRieszPositive, continuousMapRieszMeasure_mass]
  exact (norm_positive_continuousMap_functional (continuousMapPositivePart μ)
    (fun _ h => continuousMapPositivePart_nonneg μ h)).symm

theorem continuousMapRieszNegative_mass (μ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRieszNegative μ).real Set.univ = ‖continuousMapNegativePart μ‖ := by
  rw [continuousMapRieszNegative, continuousMapRieszMeasure_mass]
  exact (norm_positive_continuousMap_functional (continuousMapNegativePart μ)
    (fun _ h => continuousMapNegativePart_nonneg μ h)).symm

theorem continuousMapRiesz_total_mass (μ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRieszPositive μ).real Set.univ +
      (continuousMapRieszNegative μ).real Set.univ = ‖μ‖ := by
  rw [continuousMapRieszPositive_mass, continuousMapRieszNegative_mass]
  exact continuousMap_jordan_norm μ

/-- The representing signed measure, with no assumptions on the functional. -/
def continuousMapRieszSigned (μ : C(K, ℝ) →L[ℝ] ℝ) : SignedMeasure K :=
  (continuousMapRieszPositive μ).toSignedMeasure -
    (continuousMapRieszNegative μ).toSignedMeasure

theorem continuousMapRieszSigned_apply (μ : C(K, ℝ) →L[ℝ] ℝ)
    {s : Set K} (hs : MeasurableSet s) : continuousMapRieszSigned μ s =
      (continuousMapRieszPositive μ).real s - (continuousMapRieszNegative μ).real s :=
  Measure.toSignedMeasure_sub_apply hs

end ThesisCommon
