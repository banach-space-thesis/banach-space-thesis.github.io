import SurveyStatements.P5VectorFaithfulRetraction
import SurveyStatements.P5VectorTensorLimits

/-! Faithful contractions together with their actual strong-limit identities. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure FaithfulTreeMaps (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (H : P5Support.LpHaarPartitionTree) (hp : p ≠ ∞) where
  A : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure
  B : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure
  norm_A : ‖A‖ ≤ 1
  norm_B : ‖B‖ ≤ 1
  retraction : A.comp B = ContinuousLinearMap.id 𝕜 (Lp E p unitIntervalMeasure)
  backward_limit : ∀ f, Tendsto (fun n => VectorPartitionTree.backward
    (𝕜 := 𝕜) H hp n f) atTop (𝓝 (A f))
  forward_limit : ∀ f, Tendsto (fun n => VectorPartitionTree.forward
    (𝕜 := 𝕜) H hp n f) atTop (𝓝 (B f))

theorem exists_faithfulTreeMaps (H : P5Support.LpHaarPartitionTree)
    (hp : p ≠ ∞) (hH : H.FaithfulSplits) :
    Nonempty (FaithfulTreeMaps 𝕜 E p H hp) := by
  obtain ⟨A, B, hA, hB, hAB, _, hAlim, hBlim⟩ :=
    VectorPartitionTree.exists_faithful_retraction (𝕜 := 𝕜) (E := E) H hp hH
  exact ⟨⟨A, B, hA, hB, hAB, hAlim, hBlim⟩⟩

theorem VectorPartitionTree.backward_scalar (H : P5Support.LpHaarPartitionTree)
    (hp : p ≠ ∞) (n : ℕ) :
    VectorPartitionTree.backward (𝕜 := 𝕜) (E := 𝕜) H hp n =
      H.backward 𝕜 ⟨p, Fact.out⟩ hp n := by
  unfold VectorPartitionTree.backward P5Support.LpHaarPartitionTree.backward
  rw [vectorLpPartitionTransfer_scalar]

theorem VectorPartitionTree.forward_scalar (H : P5Support.LpHaarPartitionTree)
    (hp : p ≠ ∞) (n : ℕ) :
    VectorPartitionTree.forward (𝕜 := 𝕜) (E := 𝕜) H hp n =
      H.forward 𝕜 ⟨p, Fact.out⟩ hp n := by
  unfold VectorPartitionTree.forward P5Support.LpHaarPartitionTree.forward
  rw [vectorLpPartitionTransfer_scalar]

theorem FaithfulTreeMaps.scalar_backward_limit {H : P5Support.LpHaarPartitionTree}
    {hp : p ≠ ∞} (D : FaithfulTreeMaps 𝕜 𝕜 p H hp) (f : Lp 𝕜 p unitIntervalMeasure) :
    Tendsto (fun n => H.backward 𝕜 ⟨p, Fact.out⟩ hp n f) atTop (𝓝 (D.A f)) := by
  simpa only [VectorPartitionTree.backward_scalar] using D.backward_limit f

theorem FaithfulTreeMaps.scalar_forward_limit {H : P5Support.LpHaarPartitionTree}
    {hp : p ≠ ∞} (D : FaithfulTreeMaps 𝕜 𝕜 p H hp) (f : Lp 𝕜 p unitIntervalMeasure) :
    Tendsto (fun n => H.forward 𝕜 ⟨p, Fact.out⟩ hp n f) atTop (𝓝 (D.B f)) := by
  simpa only [VectorPartitionTree.forward_scalar] using D.forward_limit f

end SurveyStatements.P5
