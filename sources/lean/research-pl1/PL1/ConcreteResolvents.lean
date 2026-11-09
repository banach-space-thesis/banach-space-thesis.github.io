import PL1.NoiseMeasures
import PL1.ExponentialTime
import PL1.ConvolutionL1
import PL1.StrongConvergence
import PL1.DyadicProjection
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Concrete convolution resolvents and their dyadic projection

The resolvent measure is the exponential average of the actual product-noise
kernel. Its L1 operator is the genuine probability convolution constructed
on equivalence classes. The scalar multiplier formula, contraction bound,
commutation, resolvent identity, and density supply all the dyadic-system
hypotheses. No resolvent or projection existence is assumed here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal BigOperators

namespace PL1.Noise

open Walsh ExponentialTime ResolventEstimates

def resolventMeasure (rates : ℕ → ℝ≥0) (t : ℝ) : Measure Walsh.Group :=
  kernel rates ∘ₘ timeMeasure t

theorem isProbabilityMeasure_resolventMeasure (rates : ℕ → ℝ≥0) {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (resolventMeasure rates t) := by
  let := isProbabilityMeasure_timeMeasure ht
  unfold resolventMeasure
  infer_instance

/-- Fourier multipliers of the genuine exponentially averaged noise measure. -/
theorem integral_character_resolventMeasure (rates : ℕ → ℝ≥0)
    {t : ℝ} (ht : 0 < t) (F : Finset ℕ) :
    ∫ x, character F x ∂resolventMeasure rates t = (1 + t * rateSum rates F)⁻¹ := by
  let := isProbabilityMeasure_timeMeasure ht
  let := isProbabilityMeasure_resolventMeasure rates ht
  have hi : Integrable (character F) (resolventMeasure rates t) :=
    Integrable.of_bound (continuous_character F).aestronglyMeasurable 1
      (ae_of_all _ (fun x => (norm_character F x).le))
  have havg : (∫ x, character F x ∂resolventMeasure rates t) =
      ∫ u, ∫ x, character F x ∂measure rates u ∂timeMeasure t := by
    change Integrable (character F) ((kernel rates ∘ₖ Kernel.const Unit (timeMeasure t)) ()) at hi
    change (∫ x, character F x ∂((kernel rates ∘ₖ Kernel.const Unit (timeMeasure t)) ())) = _
    simpa only [Kernel.const_apply, kernel_apply] using ProbabilityTheory.Kernel.integral_comp hi
  rw [havg]
  simp only [integral_character]
  exact integral_laplace ht _ (rateSum_nonneg rates F)

abbrev PositiveTime := {t : ℝ // 0 < t}

/-- Resolvent convolution on the actual Haar L1 space, over either scalar field. -/
def resolventL1 (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0) (t : PositiveTime) :
    Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar := by
  letI := isProbabilityMeasure_resolventMeasure rates t.property
  exact convolutionL1 (resolventMeasure rates t)

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

theorem norm_resolventL1_le_one (t : PositiveTime) : ‖resolventL1 𝕜 rates t‖ ≤ 1 := by
  let := isProbabilityMeasure_resolventMeasure rates t.property
  exact norm_convolutionL1_le_one _

@[simp]
theorem resolventL1_scalarCharacter (t : PositiveTime) (F : Finset ℕ) :
    resolventL1 𝕜 rates t (scalarCharacterLp 𝕜 1 F) =
      (((1 + (t : ℝ) * rateSum rates F)⁻¹ : ℝ) : 𝕜) • scalarCharacterLp 𝕜 1 F := by
  let := isProbabilityMeasure_resolventMeasure rates t.property
  change convolutionL1 _ _ = _
  rw [convolutionL1_scalarCharacter]
  congr 2
  exact integral_character_resolventMeasure rates t.property F

theorem resolventL1_commute (s t : PositiveTime) :
    (resolventL1 𝕜 rates s).comp (resolventL1 𝕜 rates t) =
      (resolventL1 𝕜 rates t).comp (resolventL1 𝕜 rates s) := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [ContinuousLinearMap.comp_apply, resolventL1_scalarCharacter,
    map_smul, smul_smul, mul_comm]

theorem resolventL1_identity (s t : PositiveTime) :
    (ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 haar) - resolventL1 𝕜 rates s).comp
      (resolventL1 𝕜 rates t) =
    (((s : ℝ) / (t : ℝ) : ℝ) : 𝕜) • (resolventL1 𝕜 rates s).comp
      (ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 haar) - resolventL1 𝕜 rates t) := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  have hscalar := scalar_resolvent_identity s.property t.property (rateSum_nonneg rates F)
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply,
    resolventL1_scalarCharacter, map_sub, map_smul]
  calc
    _ = ((1 - (((1 + (s : ℝ) * rateSum rates F)⁻¹ : ℝ) : 𝕜)) *
        (((1 + (t : ℝ) * rateSum rates F)⁻¹ : ℝ) : 𝕜)) •
        scalarCharacterLp 𝕜 1 F := by module
    _ = ((((s : ℝ) / (t : ℝ) : ℝ) : 𝕜) *
        (((1 + (s : ℝ) * rateSum rates F)⁻¹ : ℝ) : 𝕜) *
        (1 - (((1 + (t : ℝ) * rateSum rates F)⁻¹ : ℝ) : 𝕜))) •
        scalarCharacterLp 𝕜 1 F := by
          congr 1
          exact_mod_cast hscalar
    _ = _ := by module

def dyadicTime (n : ℕ) : PositiveTime :=
  ⟨(dyadicRatio ^ 2) ^ n, pow_pos (pow_pos dyadicRatio_pos 2) n⟩

theorem tendsto_dyadicTime :
    Tendsto (fun n => (dyadicTime n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _)
  rw [dyadicRatio_sq]
  norm_num

theorem dyadic_resolvent_strong (f : Lp 𝕜 1 haar) :
    Tendsto (fun n => resolventL1 𝕜 rates (dyadicTime n) f) atTop (𝓝 f) := by
  apply tendsto_apply_of_dense_span (scalarCharacterLp 𝕜 1)
    (dense_span_scalarCharacterLp 𝕜 1 (by norm_num))
    (fun n => resolventL1 𝕜 rates (dyadicTime n))
    (ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 haar)) atTop 1
    (fun n => norm_resolventL1_le_one 𝕜 rates (dyadicTime n))
  intro F
  have hreal : Tendsto (fun n => (1 + (dyadicTime n : ℝ) * rateSum rates F)⁻¹)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_dyadicTime.mul_const (rateSum rates F)).const_add 1).inv₀ (by norm_num)
  have hcast := ((RCLike.continuous_ofReal : Continuous (fun x : ℝ => (x : 𝕜))).tendsto
    (1 : ℝ)).comp hreal
  change Tendsto (fun n => (((1 + (dyadicTime n : ℝ) * rateSum rates F)⁻¹ : ℝ) : 𝕜))
    atTop (𝓝 ((1 : ℝ) : 𝕜)) at hcast
  simpa only [resolventL1_scalarCharacter, RCLike.ofReal_one,
    one_smul, ContinuousLinearMap.id_apply] using hcast.smul_const (scalarCharacterLp 𝕜 1 F)

/-- Every nonnegative rate sequence gives a concrete dyadic system on Haar L1. -/
def dyadicSystem : DyadicSystem 𝕜 (Lp 𝕜 1 haar) where
  operator n := resolventL1 𝕜 rates (dyadicTime n)
  contractive n := norm_resolventL1_le_one 𝕜 rates (dyadicTime n)
  commute i j := resolventL1_commute 𝕜 rates (dyadicTime i) (dyadicTime j)
  resolvent i j := resolventL1_identity 𝕜 rates (dyadicTime i) (dyadicTime j)
  strong := dyadic_resolvent_strong 𝕜 rates

/-- The actual projection for the specified rates, on the ell1 sum of Haar L1. -/
def projection : L1Sum (Lp 𝕜 1 haar) →L[𝕜] L1Sum (Lp 𝕜 1 haar) :=
  (dyadicSystem 𝕜 rates).projection

theorem projection_isProjection : IsProjection (projection 𝕜 rates) :=
  (dyadicSystem 𝕜 rates).isProjection

theorem norm_projection_le : ‖projection 𝕜 rates‖ ≤ projectionBound :=
  (dyadicSystem 𝕜 rates).norm_projection_le

theorem projection_range_isClosed :
    IsClosed ((projection 𝕜 rates).range : Set (L1Sum (Lp 𝕜 1 haar))) :=
  (dyadicSystem 𝕜 rates).isClosed_projection_range

end PL1.Noise
