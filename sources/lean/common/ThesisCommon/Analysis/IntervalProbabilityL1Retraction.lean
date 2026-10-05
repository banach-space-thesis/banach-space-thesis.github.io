import ThesisCommon.Analysis.MarkovKernelL1
import ThesisCommon.Analysis.IntervalProbabilitySampler
import Mathlib.Probability.Kernel.CondDistrib

/-!
# A contractive retraction onto L1 of any probability measure on the interval

A measurable sampler gives the isometric embedding. Its genuine regular
conditional distribution gives the contractive left inverse. This avoids a
separate classification theorem for atomless measure spaces. Adapted from
the workspace PL1/IntervalRetraction construction to the pinned library.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ThesisCommon.IntervalL1Retraction

variable {𝕜 : Type*} [RCLike 𝕜]
local notation "Y" => unitInterval
variable (μ : Measure Y)

/-- An actual measurable sampler of μ on the unit interval. -/
def samplingMap : unitInterval → Y := intervalProbabilitySampler μ

theorem measurable_samplingMap : Measurable (samplingMap μ) :=
  intervalProbabilitySampler_measurable μ

variable [IsProbabilityMeasure μ]

theorem map_samplingMap : (volume : Measure unitInterval).map (samplingMap μ) = μ :=
  intervalProbabilitySampler_map μ

theorem samplingMap_measurePreserving :
    MeasurePreserving (samplingMap μ) (volume : Measure unitInterval) μ :=
  ⟨measurable_samplingMap μ, map_samplingMap μ⟩

/-- Isometric pullback along the sampler. -/
def pullback : Lp 𝕜 1 μ →ₗᵢ[𝕜] Lp 𝕜 1 (volume : Measure unitInterval) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (samplingMap μ) (samplingMap_measurePreserving μ)

theorem pullback_coeFn (u : Lp 𝕜 1 μ) :
    (pullback μ u : unitInterval → 𝕜) =ᵐ[volume] (fun x => u (samplingMap μ x)) :=
  Lp.coeFn_compMeasurePreserving u (samplingMap_measurePreserving μ)

/-- The conditional law of the original interval point given its sample. -/
def returnKernel : Kernel Y unitInterval := condDistrib id (samplingMap μ) volume

instance returnKernel_isMarkovKernel : IsMarkovKernel (returnKernel μ) := by
  unfold returnKernel
  infer_instance

theorem returnKernel_comp : returnKernel μ ∘ₘ μ = (volume : Measure unitInterval) := by
  have h := condDistrib_comp_map (measurable_samplingMap μ).aemeasurable
    (measurable_id.aemeasurable : AEMeasurable (id : unitInterval → unitInterval) volume)
  simpa only [map_samplingMap, Measure.map_id, returnKernel] using h

/-- A conditional sample remains in the fiber of the original sample. -/
theorem returnKernel_map_samplingMap :
    (returnKernel μ).map (samplingMap μ) =ᵐ[μ] Kernel.id := by
  have h := condDistrib_comp (mβ := (inferInstance : MeasurableSpace unitInterval)) (samplingMap μ)
    (measurable_id.aemeasurable : AEMeasurable (id : unitInterval → unitInterval) volume)
    (measurable_samplingMap μ)
  have hs := condDistrib_self (μ := (volume : Measure unitInterval)) (samplingMap μ)
  rw [map_samplingMap] at h hs
  simpa only [returnKernel, Function.comp_id] using h.symm.trans hs

/-- Averaging over the conditional law is a genuine contraction. -/
def retraction : Lp 𝕜 1 (volume : Measure unitInterval) →L[𝕜] Lp 𝕜 1 μ :=
  MarkovKernelL1.averageCLM μ volume (returnKernel μ) (returnKernel_comp μ)

theorem norm_retraction_le : ‖retraction (𝕜 := 𝕜) μ‖ ≤ 1 :=
  MarkovKernelL1.norm_averageCLM_le μ volume (returnKernel μ) (returnKernel_comp μ)

theorem retraction_coeFn (u : Lp 𝕜 1 (volume : Measure unitInterval)) :
    (retraction μ u : Y → 𝕜) =ᵐ[μ] (fun y => ∫ x, u x ∂returnKernel μ y) :=
  MarkovKernelL1.average_coeFn μ volume (returnKernel μ) (returnKernel_comp μ) u

/-- The interval averaging operator is a left inverse of isometric pullback. -/
@[simp] theorem retraction_pullback (u : Lp 𝕜 1 μ) : retraction μ (pullback μ u) = u := by
  apply Lp.ext
  have hcoe : ∀ᵐ y ∂μ, (pullback μ u : unitInterval → 𝕜) =ᵐ[returnKernel μ y]
      (fun x => u (samplingMap μ x)) := by
    apply Measure.ae_ae_of_ae_comp
    rw [returnKernel_comp]
    exact pullback_coeFn μ u
  filter_upwards [retraction_coeFn μ (pullback μ u), returnKernel_map_samplingMap μ, hcoe]
    with y hy hmap hcoey
  rw [hy, integral_congr_ae hcoey]
  rw [← integral_map (measurable_samplingMap μ).aemeasurable
    ((Lp.stronglyMeasurable u).aestronglyMeasurable)]
  rw [Kernel.map_apply _ (measurable_samplingMap μ)] at hmap
  rw [hmap]
  change (∫ z, u z ∂Measure.dirac y) = u y
  exact integral_dirac' u y (Lp.stronglyMeasurable u)

theorem retraction_comp_pullback :
    (retraction (𝕜 := 𝕜) μ).comp (pullback μ).toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 μ) := by
  apply ContinuousLinearMap.ext
  intro u
  exact retraction_pullback μ u

end ThesisCommon.IntervalL1Retraction




