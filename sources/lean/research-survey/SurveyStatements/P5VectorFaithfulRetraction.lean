import SurveyStatements.P5VectorPartitionTree
import SurveyStatements.P5Support.LpHaarFaithfulRetractions

/-! Faithful measured Haar trees give norm-one retractions and isometric
embeddings on the actual Banach-valued Bochner Lp space. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal Classical

namespace SurveyStatements.P5.VectorPartitionTree

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (H : P5Support.LpHaarPartitionTree)

theorem exists_faithful_retraction (hp : p ≠ ∞) (hH : H.FaithfulSplits) :
    ∃ A B : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      A.comp B = ContinuousLinearMap.id 𝕜 (Lp E p unitIntervalMeasure) ∧
      (∀ f, ‖B f‖ = ‖f‖) ∧
      (∀ f, Tendsto (fun n => backward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (A f))) ∧
      (∀ f, Tendsto (fun n => forward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (B f))) := by
  obtain ⟨B, hB, hBlim⟩ := exists_forward_limit (𝕜 := 𝕜) (E := E) H hp
  have hstable : ∀ x ∈ vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp,
      ∃ N, ∀ n ≥ N, backward (𝕜 := 𝕜) H hp n x = backward (𝕜 := 𝕜) H hp N x := by
    rintro x ⟨⟨j, c⟩, rfl⟩
    obtain ⟨N, hN⟩ := H.faithful_backward_stable_basis 𝕜 ⟨p, Fact.out⟩ hp hH j
    refine ⟨N, fun n hn => ?_⟩
    rw [backward_tensor, backward_tensor, hN n hn]
  obtain ⟨A, hA, hAlim⟩ := exists_operator_of_stable_generators
    (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)
    (vectorHaarGenerators_closure_eq_top hp) (backward (𝕜 := 𝕜) H hp)
    zero_le_one (backward_norm_le H hp) hstable
  obtain ⟨As, Bs, _, _, hAsBs, _, hAslim, hBslim⟩ :=
    H.exists_faithful_retraction 𝕜 ⟨p, Fact.out⟩ hp hH
  have hAtensor (c : E) (f : Lp 𝕜 p unitIntervalMeasure) :
      A (vectorTensor (𝕜 := 𝕜) c f) = vectorTensor (𝕜 := 𝕜) c (As f) := by
    have hv := hAlim (vectorTensor (𝕜 := 𝕜) c f)
    have hs := (vectorTensor (𝕜 := 𝕜) c).continuous.tendsto (As f) |>.comp (hAslim f)
    simp_rw [backward_tensor] at hv
    exact tendsto_nhds_unique hv hs
  have hBtensor (c : E) (f : Lp 𝕜 p unitIntervalMeasure) :
      B (vectorTensor (𝕜 := 𝕜) c f) = vectorTensor (𝕜 := 𝕜) c (Bs f) := by
    have hv := hBlim (vectorTensor (𝕜 := 𝕜) c f)
    have hs := (vectorTensor (𝕜 := 𝕜) c).continuous.tendsto (Bs f) |>.comp (hBslim f)
    simp_rw [forward_tensor] at hv
    exact tendsto_nhds_unique hv hs
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 (Lp E p unitIntervalMeasure) := by
    apply vectorOperators_eq_on_haar hp
    rintro x ⟨⟨j, c⟩, rfl⟩
    change A (B (vectorTensor (𝕜 := 𝕜) c _)) = vectorTensor (𝕜 := 𝕜) c _
    rw [hBtensor, hAtensor]
    exact congrArg (vectorTensor (𝕜 := 𝕜) c)
      (congrArg (fun L : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure =>
        L ((P5Support.intervalLpHaarBasis 𝕜 ⟨p, Fact.out⟩ hp).vector j)) hAsBs)
  refine ⟨A, B, hA, hB, hAB, fun f => ?_, hAlim, hBlim⟩
  have hab : A (B f) = f := congrArg
    (fun L : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure => L f) hAB
  apply le_antisymm
  · simpa only [one_mul] using B.le_of_opNorm_le hB f
  · calc
      ‖f‖ = ‖A (B f)‖ := congrArg norm hab.symm
      _ ≤ ‖B f‖ := by simpa only [one_mul] using A.le_of_opNorm_le hA (B f)

end SurveyStatements.P5.VectorPartitionTree
