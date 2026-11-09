import SurveyStatements.P5VectorFaithfulRetraction
import SurveyStatements.P5VectorTreeNatural
import SurveyStatements.P5Support.LpHaarRetractionMeanZero

/-! The exterior faithful-tree maps preserve actual Bochner integrals.
Consequently they preserve the outer zero-mean condition of Lp(L1). -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal Classical

namespace SurveyStatements.P5

local instance vectorTreeIntervalProbability :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem probabilityLpIntegral_eq_finite (hp : p ≠ ∞) :
    probabilityLpIntegral (𝕜 := 𝕜) (E := E) (p := p) (μ := unitIntervalMeasure) =
      finiteLpIntegral (𝕜 := 𝕜) (E := E) (μ := unitIntervalMeasure) hp := by
  apply ContinuousLinearMap.ext
  intro f
  rfl

theorem probabilityLpIntegral_scalar_eq_haar :
    probabilityLpIntegral (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := unitIntervalMeasure) =
      P5Support.lpHaarIntegral (𝕜 := 𝕜) (p := p) (μ := unitIntervalMeasure) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [probabilityLpIntegral_apply, P5Support.lpHaarIntegral_apply]
  change (@integral ℝ 𝕜 _ (NormedSpace.restrictScalars ℝ 𝕜 𝕜)
    _ unitIntervalMeasure (fun x => f x)) = ∫ x, f x ∂unitIntervalMeasure
  rw [NormedSpace.restrictScalars_eq]

theorem probabilityLpIntegral_vectorTensor (hp : p ≠ ∞)
    (c : E) (f : Lp 𝕜 p unitIntervalMeasure) :
    probabilityLpIntegral (𝕜 := 𝕜) (vectorTensor (𝕜 := 𝕜) c f) =
      probabilityLpIntegral (𝕜 := 𝕜) f • c := by
  rw [vectorTensor, probabilityLpIntegral_eq_finite hp,
    finiteLpIntegral_natural, ← probabilityLpIntegral_eq_finite hp]
  rfl

namespace VectorPartitionTree

variable (H : P5Support.LpHaarPartitionTree)

theorem backward_limit_integral (hp : p ≠ ∞) (hH : H.FaithfulSplits)
    (A : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure)
    (hA : ∀ f, Tendsto (fun n => backward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (A f)))
    (f : Lp E p unitIntervalMeasure) :
    probabilityLpIntegral (𝕜 := 𝕜) (A f) = probabilityLpIntegral (𝕜 := 𝕜) f := by
  obtain ⟨As, Bs, _, _, _, _, hAslim, _⟩ :=
    H.exists_faithful_retraction 𝕜 ⟨p, Fact.out⟩ hp hH
  have htensor (c : E) (g : Lp 𝕜 p unitIntervalMeasure) :
      A (vectorTensor (𝕜 := 𝕜) c g) = vectorTensor (𝕜 := 𝕜) c (As g) := by
    have hv := hA (vectorTensor (𝕜 := 𝕜) c g)
    have hs := (vectorTensor (𝕜 := 𝕜) c).continuous.tendsto (As g) |>.comp (hAslim g)
    simp_rw [backward_tensor] at hv
    exact tendsto_nhds_unique hv hs
  have hscalar (g : Lp 𝕜 p unitIntervalMeasure) :
      probabilityLpIntegral (𝕜 := 𝕜) (As g) = probabilityLpIntegral (𝕜 := 𝕜) g := by
    rw [probabilityLpIntegral_scalar_eq_haar]
    exact H.reading_integral 𝕜 ⟨p, Fact.out⟩ hp As hAslim g
  have he : (probabilityLpIntegral (𝕜 := 𝕜) (E := E) (p := p)
      (μ := unitIntervalMeasure)).comp A = probabilityLpIntegral := by
    apply vectorMaps_eq_on_haar hp
    rintro x ⟨⟨j, c⟩, rfl⟩
    change probabilityLpIntegral (𝕜 := 𝕜) (A (vectorTensor (𝕜 := 𝕜) c _)) =
      probabilityLpIntegral (𝕜 := 𝕜) (vectorTensor (𝕜 := 𝕜) c _)
    rw [htensor, probabilityLpIntegral_vectorTensor hp,
      probabilityLpIntegral_vectorTensor hp]
    exact congrArg (fun z : 𝕜 => z • c) (hscalar _)
  exact congrArg
    (fun L : Lp E p unitIntervalMeasure →L[𝕜] E => L f) he

theorem forward_limit_integral (hp : p ≠ ∞)
    (B : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure)
    (hB : ∀ f, Tendsto (fun n => forward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (B f)))
    (f : Lp E p unitIntervalMeasure) :
    probabilityLpIntegral (𝕜 := 𝕜) (B f) = probabilityLpIntegral (𝕜 := 𝕜) f := by
  obtain ⟨Bs, _, _, hBslim⟩ := H.exists_embedding 𝕜 ⟨p, Fact.out⟩ hp
  have htensor (c : E) (g : Lp 𝕜 p unitIntervalMeasure) :
      B (vectorTensor (𝕜 := 𝕜) c g) = vectorTensor (𝕜 := 𝕜) c (Bs g) := by
    have hv := hB (vectorTensor (𝕜 := 𝕜) c g)
    have hs := (vectorTensor (𝕜 := 𝕜) c).continuous.tendsto (Bs g) |>.comp (hBslim g)
    simp_rw [forward_tensor] at hv
    exact tendsto_nhds_unique hv hs
  have hscalar (g : Lp 𝕜 p unitIntervalMeasure) :
      probabilityLpIntegral (𝕜 := 𝕜) (Bs g) = probabilityLpIntegral (𝕜 := 𝕜) g := by
    rw [probabilityLpIntegral_scalar_eq_haar]
    exact H.embedding_integral 𝕜 ⟨p, Fact.out⟩ hp Bs hBslim g
  have he : (probabilityLpIntegral (𝕜 := 𝕜) (E := E) (p := p)
      (μ := unitIntervalMeasure)).comp B = probabilityLpIntegral := by
    apply vectorMaps_eq_on_haar hp
    rintro x ⟨⟨j, c⟩, rfl⟩
    change probabilityLpIntegral (𝕜 := 𝕜) (B (vectorTensor (𝕜 := 𝕜) c _)) =
      probabilityLpIntegral (𝕜 := 𝕜) (vectorTensor (𝕜 := 𝕜) c _)
    rw [htensor, probabilityLpIntegral_vectorTensor hp,
      probabilityLpIntegral_vectorTensor hp]
    exact congrArg (fun z : 𝕜 => z • c) (hscalar _)
  exact congrArg
    (fun L : Lp E p unitIntervalMeasure →L[𝕜] E => L f) he

end VectorPartitionTree
end SurveyStatements.P5
