import JLMS.CZeroDensity
import JLMS.MeasureCoordinates

/-!
# Atomic representation of bounded real functionals

The proof follows the classical Rudin argument: positive decomposition,
finite regular Riesz measures, and scatteredness imply an ℓ¹ expansion.
The compact-support formula extends by uniform density. All existence inputs
in this file are proved, rather than assumed representation interfaces.
-/

noncomputable section

open Set MeasureTheory Topology
open scoped CompactlySupported

namespace JLMS

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]

theorem integrable_CZero (μ : Measure K) [IsFiniteMeasure μ] (f : CZero ℝ K) :
    Integrable (fun x => f x) μ :=
  (integrable_const ‖f‖).mono' f.continuous_toFun.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_CZero_apply_le f))

/-- Integration against a finite measure as a continuous real functional. -/
def finiteMeasureIntegral (μ : Measure K) [IsFiniteMeasure μ] : CZero ℝ K →L[ℝ] ℝ :=
  ({ toFun f := ∫ x, f x ∂μ
     map_add' f g := integral_add (integrable_CZero μ f) (integrable_CZero μ g)
     map_smul' c f := integral_smul c (fun x => f x) } : CZero ℝ K →ₗ[ℝ] ℝ).mkContinuous
    (μ.real univ) (fun f => by
      simpa only [mul_comm] using norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall (norm_CZero_apply_le f)))

@[simp] theorem finiteMeasureIntegral_apply (μ : Measure K) [IsFiniteMeasure μ]
    (f : CZero ℝ K) : finiteMeasureIntegral μ f = ∫ x, f x ∂μ := rfl

variable [LocallyCompactSpace K] [T2Space K]

/-- The finite positive Riesz representation holds on all of C₀(K). -/
theorem exists_positive_atomic_representation (hK : IsScattered K)
    (φ : CZero ℝ K →L[ℝ] ℝ) (hφ : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ φ f) :
    ∃ a : ellOneOn ℝ K, (∀ x, 0 ≤ a x) ∧
      ∀ f : CZero ℝ K, φ f = ∑' x : K, a x * f x := by
  obtain ⟨μ, hfinite, hregular, hmass, hrep⟩ := exists_finite_regular_positiveRiesz hK φ hφ
  letI : IsFiniteMeasure μ := hfinite
  letI : μ.Regular := hregular
  have heq : (finiteMeasureIntegral μ : CZero ℝ K → ℝ) = φ :=
    (denseRange_compactSupportInclusion hK).equalizer
      (finiteMeasureIntegral μ).continuous φ.continuous (funext hrep)
  refine ⟨measureCoordinates μ, fun _ => ENNReal.toReal_nonneg, ?_⟩
  intro f
  rw [← heq]
  exact integral_eq_tsum_atoms_of_scattered hK μ (fun x => f x) (integrable_CZero μ f)

omit [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K] in
/-- Absolute summability of the evaluation series, for arbitrary ℓ¹ coefficients. -/
theorem summable_atomic_pairing {𝕜 : Type*} [RCLike 𝕜]
    (a : ellOneOn 𝕜 K) (f : CZero 𝕜 K) : Summable (fun x : K => a x * f x) :=
  ((ellOneOn_summable_norm a).mul_right ‖f‖).of_norm_bounded
    (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_CZero_apply_le f x) (norm_nonneg _))

/-- Rudin's existence assertion for real functionals: an actual ℓ¹ atomic series. -/
theorem exists_real_atomic_representation (hK : IsScattered K)
    (φ : CZero ℝ K →L[ℝ] ℝ) :
    ∃ a : ellOneOn ℝ K, ∀ f : CZero ℝ K, φ f = ∑' x : K, a x * f x := by
  obtain ⟨P, Q, hφ, hnP, hnQ, hp, hq⟩ := exists_positive_decomposition φ
  obtain ⟨a, ha, hPa⟩ := exists_positive_atomic_representation hK P hp
  obtain ⟨b, hb, hQb⟩ := exists_positive_atomic_representation hK Q hq
  refine ⟨a - b, ?_⟩
  intro f
  have heval : φ f = P f - Q f := by rw [hφ]; rfl
  rw [heval, hPa, hQb, ← (summable_atomic_pairing a f).tsum_sub (summable_atomic_pairing b f)]
  congr 1
  funext x
  change a x * f x - b x * f x = (a x - b x) * f x
  ring

end JLMS
