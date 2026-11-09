import SurveyStatements.P5VectorPartitionTree

/-! Strong limits of exterior tree maps act on elementary tensors by the
actual scalar tree map. These identities identify the constructed operators
on the dense tensor span used in multiplier compression. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SurveyStatements.P5.VectorPartitionTree

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (H : P5Support.LpHaarPartitionTree)

theorem forward_limit_tensor (hp : p ≠ ∞)
    (B : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure)
    (Bs : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (hB : ∀ f, Tendsto (fun n => forward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (B f)))
    (hBs : ∀ f, Tendsto (fun n => H.forward 𝕜 ⟨p, Fact.out⟩ hp n f)
      atTop (𝓝 (Bs f))) (c : E) (f : Lp 𝕜 p unitIntervalMeasure) :
    B (vectorTensor (𝕜 := 𝕜) c f) = vectorTensor (𝕜 := 𝕜) c (Bs f) := by
  have hv := hB (vectorTensor (𝕜 := 𝕜) c f)
  have hs := (vectorTensor (𝕜 := 𝕜) c).continuous.tendsto (Bs f) |>.comp (hBs f)
  simp_rw [forward_tensor] at hv
  exact tendsto_nhds_unique hv hs

theorem backward_limit_tensor (hp : p ≠ ∞)
    (A : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure)
    (As : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (hA : ∀ f, Tendsto (fun n => backward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (A f)))
    (hAs : ∀ f, Tendsto (fun n => H.backward 𝕜 ⟨p, Fact.out⟩ hp n f)
      atTop (𝓝 (As f))) (c : E) (f : Lp 𝕜 p unitIntervalMeasure) :
    A (vectorTensor (𝕜 := 𝕜) c f) = vectorTensor (𝕜 := 𝕜) c (As f) := by
  have hv := hA (vectorTensor (𝕜 := 𝕜) c f)
  have hs := (vectorTensor (𝕜 := 𝕜) c).continuous.tendsto (As f) |>.comp (hAs f)
  simp_rw [backward_tensor] at hv
  exact tendsto_nhds_unique hv hs

end SurveyStatements.P5.VectorPartitionTree
