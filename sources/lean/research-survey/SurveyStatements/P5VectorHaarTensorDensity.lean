import SurveyStatements.P5VectorPartitionNatural
import SurveyStatements.P5HaarDensityStep
import SurveyStatements.P5Support.LpHaarSchauderBasis

/-! Scalar Haar basis vectors tensored with arbitrary Banach-valued
constants generate a norm-dense submodule of the actual Bochner Lp space. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def vectorTensor (c : E) :
    Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure :=
  ((ContinuousLinearMap.id 𝕜 𝕜).smulRight c).compLpL p unitIntervalMeasure

theorem vectorTensor_indicator (s : Set ℝ) (hs : MeasurableSet s) (c : E) :
    vectorTensor (𝕜 := 𝕜) (p := p) c
      (indicatorConstLp p hs (measure_ne_top unitIntervalMeasure s) (1 : 𝕜)) =
      indicatorConstLp p hs (measure_ne_top unitIntervalMeasure s) c := by
  rw [vectorTensor, compLpL_indicator]
  simp

def vectorHaarGenerators (hp : p ≠ ∞) : Set (Lp E p unitIntervalMeasure) :=
  Set.range (fun jc : ℕ × E => vectorTensor (𝕜 := 𝕜) jc.2
    ((P5Support.intervalLpHaarBasis 𝕜 ⟨p, Fact.out⟩ hp).vector jc.1))

theorem vectorTensor_mem_closed_haarSpan (hp : p ≠ ∞)
    (c : E) (f : Lp 𝕜 p unitIntervalMeasure) :
    vectorTensor (𝕜 := 𝕜) c f ∈
      (Submodule.span 𝕜 (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)).topologicalClosure := by
  let b := P5Support.intervalLpHaarBasis 𝕜 ⟨p, Fact.out⟩ hp
  let S := (Submodule.span 𝕜 (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)).topologicalClosure
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    ((vectorTensor (𝕜 := 𝕜) c).continuous.tendsto f |>.comp (b.expansion f))
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [map_sum]
  apply S.sum_mem
  intro j _
  rw [map_smul]
  apply S.smul_mem
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨(j, c), rfl⟩

theorem vectorHaarGenerators_closure_eq_top (hp : p ≠ ∞) :
    (Submodule.span 𝕜 (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)).topologicalClosure = ⊤ := by
  let S := (Submodule.span 𝕜 (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)).topologicalClosure
  have hstep : haarDensityStepSpace (𝕜 := 𝕜) (E := E) (p := p) ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨I, c⟩, rfl⟩
    change indicatorConstLp p (s := haarDensityCell I) measurableSet_Ico
      (measure_ne_top unitIntervalMeasure _) c ∈ S
    rw [← vectorTensor_indicator (𝕜 := 𝕜) (haarDensityCell I) measurableSet_Ico c]
    exact vectorTensor_mem_closed_haarSpan hp c _
  have htop := Submodule.topologicalClosure_minimal _ hstep
    (Submodule.isClosed_topologicalClosure _)
  rw [haarDensityStepSpace_closure_eq_top hp] at htop
  exact top_unique htop

theorem vectorMaps_eq_on_haar {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (hp : p ≠ ∞) (T U : Lp E p unitIntervalMeasure →L[𝕜] F)
    (hTU : Set.EqOn T U (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)) : T = U := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.eqOn_closure_span hTU
  change x ∈ (Submodule.span 𝕜 (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)).topologicalClosure
  rw [vectorHaarGenerators_closure_eq_top hp]
  trivial

theorem vectorOperators_eq_on_haar (hp : p ≠ ∞)
    (T U : Lp E p unitIntervalMeasure →L[𝕜] Lp E p unitIntervalMeasure)
    (hTU : Set.EqOn T U (vectorHaarGenerators (𝕜 := 𝕜) (E := E) hp)) : T = U :=
  vectorMaps_eq_on_haar hp T U hTU

end SurveyStatements.P5
