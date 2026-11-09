import SurveyStatements.P5VectorPartitionScalar
import SurveyStatements.P5VectorHaarTensorDensity
import SurveyStatements.P5StableGeneratorLimit
import SurveyStatements.P5Support.LpHaarPartitionEmbedding

/-! Actual exterior operators for measured binary partition trees.
The forward operators have a contractive strong limit on Bochner Lp. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal Classical

namespace SurveyStatements.P5

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace VectorPartitionTree

variable (H : P5Support.LpHaarPartitionTree)

def forward (hp : p ≠ ∞) (n : ℕ) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  vectorLpPartitionTransfer hp
    (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k) (H.cell n) (H.measurable n)

def backward (hp : p ≠ ∞) (n : ℕ) :
    Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  vectorLpPartitionTransfer hp (H.cell n)
    (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k) (fun _ => measurableSet_Ioc)

theorem forward_norm_le (hp : p ≠ ∞) (n : ℕ) :
    ‖forward (𝕜 := 𝕜) (E := E) H hp n‖ ≤ 1 := by
  apply norm_vectorLpPartitionTransfer_le hp _ _ (fun _ => measurableSet_Ioc)
    (H.measurable n) (P5Support.lpHaarLevelCells_disjoint n) (H.disjoint n)
    (P5Support.lpHaarLevelCells_cover n) (H.cover n)
    (P5Support.lpHaarLevelCells_nonzero n)
  intro k
  exact (P5Support.lpHaarCell_measure n k k.isLt).trans (H.measure n k).symm

theorem backward_norm_le (hp : p ≠ ∞) (n : ℕ) :
    ‖backward (𝕜 := 𝕜) (E := E) H hp n‖ ≤ 1 := by
  apply norm_vectorLpPartitionTransfer_le hp _ _ (H.measurable n)
    (fun _ => measurableSet_Ioc) (H.disjoint n) (P5Support.lpHaarLevelCells_disjoint n)
    (H.cover n) (P5Support.lpHaarLevelCells_cover n) (H.cell_nonzero n)
  intro k
  exact (H.measure n k).trans (P5Support.lpHaarCell_measure n k k.isLt).symm

theorem forward_tensor (hp : p ≠ ∞) (n : ℕ) (c : E)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    forward (𝕜 := 𝕜) H hp n (vectorTensor (𝕜 := 𝕜) c f) =
      vectorTensor (𝕜 := 𝕜) c (H.forward 𝕜 ⟨p, Fact.out⟩ hp n f) := by
  unfold forward vectorTensor
  rw [vectorLpPartitionTransfer_natural, vectorLpPartitionTransfer_scalar]
  rfl

theorem backward_tensor (hp : p ≠ ∞) (n : ℕ) (c : E)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    backward (𝕜 := 𝕜) H hp n (vectorTensor (𝕜 := 𝕜) c f) =
      vectorTensor (𝕜 := 𝕜) c (H.backward 𝕜 ⟨p, Fact.out⟩ hp n f) := by
  unfold backward vectorTensor
  rw [vectorLpPartitionTransfer_natural, vectorLpPartitionTransfer_scalar]
  rfl

theorem exists_forward_limit (hp : p ≠ ∞) :
    ∃ B : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure,
      ‖B‖ ≤ 1 ∧ ∀ f,
        Tendsto (fun n => forward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (B f)) := by
  apply exists_operator_of_stable_generators
    (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)
    (vectorHaarGenerators_closure_eq_top hp) (forward (𝕜 := 𝕜) H hp)
    zero_le_one (forward_norm_le H hp)
  rintro x ⟨⟨j, c⟩, rfl⟩
  obtain ⟨N, hN⟩ := H.forward_stable_basis 𝕜 ⟨p, Fact.out⟩ hp j
  refine ⟨N, fun n hn => ?_⟩
  rw [forward_tensor, forward_tensor, hN n hn]

end VectorPartitionTree
end SurveyStatements.P5
