import PL1.WalshModel
import PL1.ConvolutionL1
import PL1.RNPBridge
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Singular measures and the Walsh spectral obstruction

For a finite positive measure, all Walsh coefficients determine the measure.
A measure charging a Haar-null set therefore cannot have the Walsh coefficients
of an integrable real density. This is the scalar obstruction needed for the
nonrepresentability of singular convolution.
-/

noncomputable section
universe u

open MeasureTheory
open scoped ENNReal Topology BigOperators

namespace PL1
namespace SingularConvolution

open Walsh

/-- Integration on continuous functions on the compact sign group, as a bounded functional. -/
def continuousIntegral (μ : Measure Walsh.Group) [IsFiniteMeasure μ] : C(Walsh.Group, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM : Lp ℝ 1 μ →L[ℝ] ℝ).comp (ContinuousMap.toLp 1 μ ℝ)

theorem continuousIntegral_apply (μ : Measure Walsh.Group) [IsFiniteMeasure μ]
    (f : C(Walsh.Group, ℝ)) : continuousIntegral μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp μ f)

/-- All Walsh coefficients determine a finite positive Borel measure. -/
theorem measure_eq_of_walsh_integrals (μ ν : Measure Walsh.Group)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ F : Finset ℕ, ∫ x, character F x ∂μ = ∫ x, character F x ∂ν) : μ = ν := by
  have hi : continuousIntegral μ = continuousIntegral ν := by
    apply ContinuousLinearMap.ext_on (s := Set.range characterContinuous)
    · rw [← polynomials_toSubmodule]
      exact polynomials_dense
    · rintro f ⟨F, rfl⟩
      rw [continuousIntegral_apply, continuousIntegral_apply]
      exact h F
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hh := congrArg (fun T => T f.toContinuousMap) hi
  rw [continuousIntegral_apply, continuousIntegral_apply] at hh
  exact hh

theorem integrable_character_measure (μ : Measure Walsh.Group) [IsFiniteMeasure μ]
    (F : Finset ℕ) : Integrable (character F) μ := by
  apply Integrable.of_bound (continuous_character F).aestronglyMeasurable 1
  exact ae_of_all _ (fun x => (norm_character F x).le)

/-- The measure with positive part of a real density. -/
def positiveDensityMeasure (g : Walsh.Group → ℝ) : Measure Walsh.Group :=
  haar.withDensity (fun x => ENNReal.ofReal (g x))

theorem positiveDensityMeasure_finite {g : Walsh.Group → ℝ} (hg : Integrable g haar) :
    IsFiniteMeasure (positiveDensityMeasure g) := by
  exact isFiniteMeasure_withDensity_ofReal hg.hasFiniteIntegral

theorem integral_positiveDensityMeasure {g : Walsh.Group → ℝ} (hg : Integrable g haar)
    (f : Walsh.Group → ℝ) :
    ∫ x, f x ∂positiveDensityMeasure g = ∫ x, max (g x) 0 * f x ∂haar := by
  rw [positiveDensityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]

/-- Matching Walsh moments of an integrable density gives equality after moving its negative
part to the positive-measure side. -/
theorem measure_add_negativeDensity_eq_positiveDensity
    (ν : Measure Walsh.Group) [IsFiniteMeasure ν]
    {g : Walsh.Group → ℝ} (hg : Integrable g haar)
    (hMom : ∀ F : Finset ℕ,
      ∫ x, character F x * g x ∂haar = ∫ x, character F x ∂ν) :
    ν + positiveDensityMeasure (fun x => -g x) = positiveDensityMeasure g := by
  let := positiveDensityMeasure_finite hg
  let := positiveDensityMeasure_finite hg.neg
  apply measure_eq_of_walsh_integrals
  intro F
  rw [integral_add_measure (integrable_character_measure ν F)
    (integrable_character_measure _ F)]
  rw [integral_positiveDensityMeasure (g := fun x => -g x) hg.neg,
    integral_positiveDensityMeasure hg, ← hMom F]
  have hchar : AEStronglyMeasurable (character F) haar := (continuous_character F).aestronglyMeasurable
  have hb : ∀ᵐ x ∂haar, ‖character F x‖ ≤ 1 := ae_of_all _ (fun x => (norm_character F x).le)
  rw [← integral_add (hg.bdd_mul hchar hb) (hg.neg_part.mul_bdd hchar hb)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    have hparts : g x + max (-g x) 0 = max (g x) 0 := by
      linarith [max_zero_sub_max_neg_zero_eq_self (g x)]
    calc
      character F x * g x + max (-g x) 0 * character F x =
          (g x + max (-g x) 0) * character F x := by ring
      _ = max (g x) 0 * character F x := by rw [hparts])

/-- A finite measure charging a Haar-null set cannot have the Walsh moments of an L1 density. -/
theorem no_integrable_density_of_null_carrier
    (ν : Measure Walsh.Group) [IsFiniteMeasure ν] (N : Set Walsh.Group)
    (hmN : haar N = 0) (hνN : ν N ≠ 0) :
    ¬ ∃ g : Walsh.Group → ℝ, Integrable g haar ∧
      ∀ F : Finset ℕ, ∫ x, character F x * g x ∂haar = ∫ x, character F x ∂ν := by
  rintro ⟨g, hg, hMom⟩
  have heq := measure_add_negativeDensity_eq_positiveDensity ν hg hMom
  have hp : positiveDensityMeasure g N = 0 :=
    withDensity_absolutelyContinuous haar _ hmN
  have hn : positiveDensityMeasure (fun x => -g x) N = 0 :=
    withDensity_absolutelyContinuous haar _ hmN
  have hev := congrArg (fun μ : Measure Walsh.Group => μ N) heq
  rw [Measure.add_apply, hp, hn, add_zero] at hev
  exact hνN hev

/-- The Walsh coefficient functional on actual Haar L1. -/
def fourierFunctional (F : Finset ℕ) : Lp ℝ 1 haar →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing haar ∞ 1 (characterLp ∞ F)

theorem fourierFunctional_apply (F : Finset ℕ) (f : Lp ℝ 1 haar) :
    fourierFunctional F f = ∫ x, character F x * f x ∂haar := by
  rw [fourierFunctional, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [coeFn_characterLp ∞ F] with x hx
  simp only [ContinuousLinearMap.mul_apply', hx]

theorem fourierFunctional_character (F H : Finset ℕ) :
    fourierFunctional F (characterLp 1 H) = if F = H then 1 else 0 := by
  rw [fourierFunctional_apply, ← integral_character_mul F H]
  apply integral_congr_ae
  filter_upwards [coeFn_characterLp 1 H] with x hx
  rw [hx]

/-- The Fourier functionals diagonalize probability convolution on all of L1. -/
theorem fourierFunctional_convolution (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (F : Finset ℕ) :
    (fourierFunctional F).comp (convolutionL1 ν) = coefficient ν F • fourierFunctional F := by
  apply ContinuousLinearMap.ext_on (dense_span_characterLp 1 (by norm_num))
  rintro x ⟨H, rfl⟩
  simp only [ContinuousLinearMap.comp_apply, convolutionL1_character, map_smul,
    smul_apply, fourierFunctional_character, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp

theorem fourierFunctional_convolution_apply (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (F : Finset ℕ) (f : Lp ℝ 1 haar) :
    fourierFunctional F (convolutionL1 ν f) = coefficient ν F * fourierFunctional F f := by
  exact congrArg (fun T : Lp ℝ 1 haar →L[ℝ] ℝ => T f)
    (fourierFunctional_convolution ν F)

theorem fourierFunctional_indicator (F : Finset ℕ) (A : Set Walsh.Group)
    (hA : MeasurableSet A) :
    fourierFunctional F (RNPBridge.indicatorL1 haar A) = ∫ x in A, character F x ∂haar := by
  rw [fourierFunctional_apply, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [RNPBridge.indicatorL1_coeFn haar hA] with x hx
  rw [hx]
  by_cases hxA : x ∈ A <;> simp [hxA]

/-- A setwise Bochner density for convolution forces every Walsh coefficient of that density. -/
theorem fourier_setwise_density (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    {b : Walsh.Group → Lp ℝ 1 haar} (hb : Integrable b haar)
    (hrep : ∀ A : Set Walsh.Group, MeasurableSet A →
      convolutionL1 ν (RNPBridge.indicatorL1 haar A) = ∫ x in A, b x ∂haar)
    (F : Finset ℕ) :
    (fun x => fourierFunctional F (b x)) =ᵐ[haar]
      fun x => coefficient ν F * character F x := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((fourierFunctional F).integrable_comp hb) ((integrable_character F).const_mul _)
  intro A hA _
  rw [(fourierFunctional F).integral_comp_comm hb.integrableOn, ← hrep A hA,
    fourierFunctional_convolution_apply, fourierFunctional_indicator F A hA,
    integral_const_mul]

theorem integral_character_translate (F : Finset ℕ) (f : Lp ℝ 1 haar) (s : Walsh.Group) :
    ∫ x, character F x * f (s * x) ∂haar = character F s * fourierFunctional F f := by
  calc
    _ = ∫ x, character F s * (character F (s * x) * f (s * x)) ∂haar := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [character_mul, ← mul_assoc, character_mul_self, one_mul])
    _ = character F s * ∫ x, character F (s * x) * f (s * x) ∂haar :=
      integral_const_mul _ _
    _ = character F s * ∫ x, character F x * f x ∂haar := by
      rw [integral_mul_left_eq_self (fun x => character F x * f x) s]
    _ = _ := by rw [fourierFunctional_apply]

/-- Countability of the Walsh system turns a setwise L1-valued density into a scalar density
with the same Fourier coefficients as the convolving measure. -/
theorem exists_integrable_density_of_setwise_representation
    (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    {b : Walsh.Group → Lp ℝ 1 haar} (hb : Integrable b haar)
    (hrep : ∀ A : Set Walsh.Group, MeasurableSet A →
      convolutionL1 ν (RNPBridge.indicatorL1 haar A) = ∫ x in A, b x ∂haar) :
    ∃ g : Walsh.Group → ℝ, Integrable g haar ∧
      ∀ F : Finset ℕ, ∫ x, character F x * g x ∂haar = ∫ x, character F x ∂ν := by
  have hsim : ∀ᵐ x ∂haar, ∀ F : Finset ℕ,
      fourierFunctional F (b x) = coefficient ν F * character F x := by
    exact ae_all_iff.mpr (fun F => fourier_setwise_density ν hb hrep F)
  obtain ⟨s, hs⟩ := hsim.exists
  refine ⟨fun x => b s (s * x), (L1.integrable_coeFn (b s)).comp_mul_left s, ?_⟩
  intro F
  rw [integral_character_translate, hs F]
  calc
    character F s * (coefficient ν F * character F s) =
        coefficient ν F * (character F s * character F s) := by ring
    _ = _ := by rw [character_mul_self, mul_one]; rfl

/-- Singular probability convolution admits no integrable setwise Bochner density into L1. -/
theorem no_setwise_density_of_null_carrier
    (ν : Measure Walsh.Group) [IsProbabilityMeasure ν] (N : Set Walsh.Group)
    (hmN : haar N = 0) (hνN : ν N ≠ 0) :
    ¬ ∃ b : Walsh.Group → Lp ℝ 1 haar, Integrable b haar ∧
      ∀ A : Set Walsh.Group, MeasurableSet A →
        convolutionL1 ν (RNPBridge.indicatorL1 haar A) = ∫ x in A, b x ∂haar := by
  rintro ⟨b, hb, hrep⟩
  exact no_integrable_density_of_null_carrier ν N hmN hνN
    (exists_integrable_density_of_setwise_representation ν hb hrep)

/-- Every Banach space through which singular probability convolution factors fails the
reviewed Radon–Nikodym property. -/
theorem not_RNP_of_convolution_factorization
    (ν : Measure Walsh.Group) [IsProbabilityMeasure ν] (N : Set Walsh.Group)
    (hmN : haar N = 0) (hνN : ν N ≠ 0)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Lp ℝ 1 haar →L[ℝ] E) (T : E →L[ℝ] Lp ℝ 1 haar)
    (hfac : T.comp S = convolutionL1 ν) : ¬ HasRadonNikodymProperty.{u, 0} E := by
  intro hE
  obtain ⟨b, hb, hrep⟩ := RNPBridge.exists_setwise_density_of_RNP haar hE S
  apply no_setwise_density_of_null_carrier ν N hmN hνN
  refine ⟨fun x => T (b x), T.integrable_comp hb, ?_⟩
  intro A hA
  rw [T.integral_comp_comm hb.integrableOn, ← hrep A hA, ← hfac]
  rfl

end SingularConvolution
end PL1
