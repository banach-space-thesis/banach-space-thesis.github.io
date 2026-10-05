import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual contractive integration against a Markov kernel. Adapted from the
workspace PL1/KernelL1 construction to the pinned thesis library. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ThesisCommon.MarkovKernelL1

variable {𝕜 α β : Type*} [RCLike 𝕜] [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β) (κ : Kernel α β)
variable (hcomp : κ ∘ₘ μ = ν)

/-- Integrate the genuine L1 representative against the transition probability. -/
def averageFunction (u : Lp 𝕜 1 ν) (x : α) : 𝕜 := ∫ y, u y ∂κ x

include hcomp

theorem integrable_comp (u : Lp 𝕜 1 ν) : Integrable (u : β → 𝕜) (κ ∘ₘ μ) := by
  rw [hcomp]
  exact L1.integrable_coeFn u

theorem ae_integrable (u : Lp 𝕜 1 ν) : ∀ᵐ x ∂μ, Integrable (u : β → 𝕜) (κ x) :=
  Measure.ae_integrable_of_integrable_comp (integrable_comp μ ν κ hcomp u)

theorem integrable_averageFunction (u : Lp 𝕜 1 ν) :
    Integrable (averageFunction ν κ u) μ := by
  apply Integrable.mono'
    (Measure.integrable_integral_norm_of_integrable_comp (integrable_comp μ ν κ hcomp u))
    (Lp.stronglyMeasurable u).integral_kernel.aestronglyMeasurable
  exact ae_of_all _ (fun x => norm_integral_le_integral_norm _)

/-- The L1 class of integration against a probability kernel. -/
def average (u : Lp 𝕜 1 ν) : Lp 𝕜 1 μ :=
  (integrable_averageFunction μ ν κ hcomp u).toL1 _

theorem average_coeFn (u : Lp 𝕜 1 ν) :
    (average μ ν κ hcomp u : α → 𝕜) =ᵐ[μ] averageFunction ν κ u :=
  (integrable_averageFunction μ ν κ hcomp u).coeFn_toL1

theorem norm_average_le [IsMarkovKernel κ] (u : Lp 𝕜 1 ν) : ‖average μ ν κ hcomp u‖ ≤ ‖u‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖average μ ν κ hcomp u x‖ ∂μ) = ∫ x, ‖averageFunction ν κ u x‖ ∂μ :=
      integral_congr_ae ((average_coeFn μ ν κ hcomp u).fun_comp norm)
    _ ≤ ∫ x, ∫ y, ‖u y‖ ∂κ x ∂μ :=
      integral_mono (integrable_averageFunction μ ν κ hcomp u).norm
        (Measure.integrable_integral_norm_of_integrable_comp (integrable_comp μ ν κ hcomp u))
        (fun x => norm_integral_le_integral_norm _)
    _ = ∫ y, ‖u y‖ ∂ν := by
      have h := ProbabilityTheory.Kernel.integral_comp
        (κ := Kernel.const Unit μ) (η := κ) (a := ())
        (f := fun y => ‖u y‖)
        (by simpa [← Measure.comp_eq_comp_const_apply] using (integrable_comp μ ν κ hcomp u).norm)
      simpa [← Measure.comp_eq_comp_const_apply, hcomp] using h.symm

theorem average_add (u v : Lp 𝕜 1 ν) :
    average μ ν κ hcomp (u + v) = average μ ν κ hcomp u + average μ ν κ hcomp v := by
  apply Lp.ext
  have huv : ∀ᵐ x ∂μ, (u + v : Lp 𝕜 1 ν) =ᵐ[κ x] (fun y => u y + v y) := by
    apply Measure.ae_ae_of_ae_comp
    rw [hcomp]
    exact Lp.coeFn_add u v
  filter_upwards [average_coeFn μ ν κ hcomp (u + v), average_coeFn μ ν κ hcomp u,
    average_coeFn μ ν κ hcomp v, Lp.coeFn_add (average μ ν κ hcomp u) (average μ ν κ hcomp v),
    ae_integrable μ ν κ hcomp u, ae_integrable μ ν κ hcomp v, huv] with x ha hu hv hab hui hvi huvx
  rw [ha, hab, Pi.add_apply, hu, hv]
  exact (integral_congr_ae huvx).trans (integral_add hui hvi)

theorem average_smul (c : 𝕜) (u : Lp 𝕜 1 ν) :
    average μ ν κ hcomp (c • u) = c • average μ ν κ hcomp u := by
  apply Lp.ext
  have hcu : ∀ᵐ x ∂μ, (c • u : Lp 𝕜 1 ν) =ᵐ[κ x] (fun y => c • u y) := by
    apply Measure.ae_ae_of_ae_comp
    rw [hcomp]
    exact Lp.coeFn_smul c u
  filter_upwards [average_coeFn μ ν κ hcomp (c • u), average_coeFn μ ν κ hcomp u,
    Lp.coeFn_smul c (average μ ν κ hcomp u), hcu] with x ha hu hsm hcx
  rw [ha, hsm, Pi.smul_apply, hu]
  exact (integral_congr_ae hcx).trans (integral_smul c _)

/-- A probability kernel whose average measure is ν induces a contraction L1(ν)→L1(μ). -/
def averageCLM [IsMarkovKernel κ] : Lp 𝕜 1 ν →L[𝕜] Lp 𝕜 1 μ :=
  LinearMap.mkContinuous
    { toFun := average μ ν κ hcomp
      map_add' := average_add μ ν κ hcomp
      map_smul' := by intro c u; exact average_smul μ ν κ hcomp c u }
    1 (by intro u; simpa using norm_average_le μ ν κ hcomp u)

@[simp] theorem averageCLM_apply [IsMarkovKernel κ] (u : Lp 𝕜 1 ν) :
    averageCLM μ ν κ hcomp u = average μ ν κ hcomp u := rfl

theorem norm_averageCLM_le [IsMarkovKernel κ] : ‖averageCLM (𝕜 := 𝕜) μ ν κ hcomp‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun u => by simpa using norm_average_le μ ν κ hcomp u)

end ThesisCommon.MarkovKernelL1



