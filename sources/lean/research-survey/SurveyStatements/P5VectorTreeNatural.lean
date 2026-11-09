import SurveyStatements.P5VectorPartitionTree

/-! Strong limits of the actual exterior operators commute with bounded
maps on the value space. This includes the inner expectation of Lp(L1). -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace SurveyStatements.P5.VectorPartitionTree

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (H : P5Support.LpHaarPartitionTree)

theorem forward_limit_natural (hp : p ≠ ∞)
    (B : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure)
    (BF : Lp F p unitIntervalMeasure →L[𝕜] Lp F p unitIntervalMeasure)
    (hB : ∀ f, Tendsto (fun n => forward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (B f)))
    (hBF : ∀ f, Tendsto (fun n => forward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (BF f)))
    (L : E →L[𝕜] F) (f : Lp E p unitIntervalMeasure) :
    BF (L.compLpL p unitIntervalMeasure f) = L.compLpL p unitIntervalMeasure (B f) := by
  have h₁ := hBF (L.compLpL p unitIntervalMeasure f)
  have h₂ := (L.compLpL p unitIntervalMeasure).continuous.tendsto (B f) |>.comp (hB f)
  simp_rw [forward, vectorLpPartitionTransfer_natural] at h₁
  exact tendsto_nhds_unique h₁ h₂

theorem backward_limit_natural (hp : p ≠ ∞)
    (A : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure)
    (AF : Lp F p unitIntervalMeasure →L[𝕜] Lp F p unitIntervalMeasure)
    (hA : ∀ f, Tendsto (fun n => backward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (A f)))
    (hAF : ∀ f, Tendsto (fun n => backward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (AF f)))
    (L : E →L[𝕜] F) (f : Lp E p unitIntervalMeasure) :
    AF (L.compLpL p unitIntervalMeasure f) = L.compLpL p unitIntervalMeasure (A f) := by
  have h₁ := hAF (L.compLpL p unitIntervalMeasure f)
  have h₂ := (L.compLpL p unitIntervalMeasure).continuous.tendsto (A f) |>.comp (hA f)
  simp_rw [backward, vectorLpPartitionTransfer_natural] at h₁
  exact tendsto_nhds_unique h₁ h₂

end SurveyStatements.P5.VectorPartitionTree
