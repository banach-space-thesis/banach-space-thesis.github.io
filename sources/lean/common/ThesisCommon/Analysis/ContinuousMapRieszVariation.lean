import ThesisCommon.Analysis.ContinuousMapRiesz
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

/-! The positive and negative Riesz measures are the canonical Jordan decomposition.
The proof uses the sharp functional norm identity and minimality under cancellation. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

theorem continuousMap_integrable_finite (ν : Measure K) [IsFiniteMeasure ν]
    (f : C(K, ℝ)) : Integrable f ν :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem norm_continuousMap_functional_le_representation_mass
    (μ : C(K, ℝ) →L[ℝ] ℝ) (P N : Measure K) [IsFiniteMeasure P] [IsFiniteMeasure N]
    (h : ∀ f : C(K, ℝ), μ f = (∫ t, f t ∂P) - ∫ t, f t ∂N) :
    ‖μ‖ ≤ P.real Set.univ + N.real Set.univ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (measureReal_nonneg) measureReal_nonneg)
  intro f
  rw [h f]
  have hp := norm_integral_le_of_norm_le_const (μ := P)
    (Filter.Eventually.of_forall fun t => f.norm_coe_le_norm t)
  have hn := norm_integral_le_of_norm_le_const (μ := N)
    (Filter.Eventually.of_forall fun t => f.norm_coe_le_norm t)
  calc
    ‖(∫ t, f t ∂P) - ∫ t, f t ∂N‖ ≤ ‖∫ t, f t ∂P‖ + ‖∫ t, f t ∂N‖ := norm_sub_le _ _
    _ ≤ ‖f‖ * P.real Set.univ + ‖f‖ * N.real Set.univ := add_le_add hp hn
    _ = (P.real Set.univ + N.real Set.univ) * ‖f‖ := by ring

theorem finiteMeasure_cancel_balance (P N : Measure K)
    [IsFiniteMeasure P] [IsFiniteMeasure N] : P + (N - P) = (P - N) + N := by
  apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
  exact sub_eq_sub_iff_add_eq_add.mp Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub

theorem continuousMap_integral_cancel_balance (P N : Measure K)
    [IsFiniteMeasure P] [IsFiniteMeasure N] (f : C(K, ℝ)) :
    (∫ t, f t ∂P) - ∫ t, f t ∂N =
      (∫ t, f t ∂(P - N)) - ∫ t, f t ∂(N - P) := by
  have h := congrArg (fun ν : Measure K => ∫ t, f t ∂ν) (finiteMeasure_cancel_balance P N)
  dsimp only at h
  rw [integral_add_measure (continuousMap_integrable_finite P f)
      (continuousMap_integrable_finite (N - P) f),
    integral_add_measure (continuousMap_integrable_finite (P - N) f)
      (continuousMap_integrable_finite N f)] at h
  linarith

theorem continuousMapRiesz_sub_eq (μ : C(K, ℝ) →L[ℝ] ℝ) :
    continuousMapRieszPositive μ - continuousMapRieszNegative μ = continuousMapRieszPositive μ ∧
      continuousMapRieszNegative μ - continuousMapRieszPositive μ = continuousMapRieszNegative μ := by
  let P := continuousMapRieszPositive μ
  let N := continuousMapRieszNegative μ
  have hb : ‖μ‖ ≤ (P - N).real Set.univ + (N - P).real Set.univ :=
    norm_continuousMap_functional_le_representation_mass μ (P - N) (N - P)
      (fun f => (continuousMap_real_riesz_representation μ f).trans
        (continuousMap_integral_cancel_balance P N f))
  have hp : (P - N).real Set.univ ≤ P.real Set.univ :=
    ENNReal.toReal_mono (measure_ne_top P _) (Measure.sub_le Set.univ)
  have hn : (N - P).real Set.univ ≤ N.real Set.univ :=
    ENNReal.toReal_mono (measure_ne_top N _) (Measure.sub_le Set.univ)
  have htotal : P.real Set.univ + N.real Set.univ = ‖μ‖ := continuousMapRiesz_total_mass μ
  constructor
  · apply Measure.eq_of_le_of_measure_univ_eq Measure.sub_le
    apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
    linarith
  · apply Measure.eq_of_le_of_measure_univ_eq Measure.sub_le
    apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
    linarith

theorem continuousMapRiesz_mutuallySingular (μ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRieszPositive μ).MutuallySingular (continuousMapRieszNegative μ) := by
  have h := Measure.mutually_singular_measure_sub
    (μ := continuousMapRieszPositive μ) (ν := continuousMapRieszNegative μ)
  rwa [(continuousMapRiesz_sub_eq μ).1, (continuousMapRiesz_sub_eq μ).2] at h

theorem continuousMapRieszSigned_totalVariation (μ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRieszSigned μ).totalVariation =
      continuousMapRieszPositive μ + continuousMapRieszNegative μ := by
  rw [continuousMapRieszSigned, SignedMeasure.totalVariation,
    Measure.toJordanDecomposition_toSignedMeasure_sub]
  change (continuousMapRieszPositive μ - continuousMapRieszNegative μ) +
    (continuousMapRieszNegative μ - continuousMapRieszPositive μ) = _
  rw [(continuousMapRiesz_sub_eq μ).1, (continuousMapRiesz_sub_eq μ).2]

theorem continuousMapRieszSigned_variation_norm (μ : C(K, ℝ) →L[ℝ] ℝ) :
    (continuousMapRieszSigned μ).totalVariation.real Set.univ = ‖μ‖ := by
  rw [continuousMapRieszSigned_totalVariation, measureReal_add_apply,
    continuousMapRiesz_total_mass]

end ThesisCommon
