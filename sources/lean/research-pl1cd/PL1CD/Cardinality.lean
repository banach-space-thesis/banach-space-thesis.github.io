import PL1CD.Statements
import PL1.IntervalSubtype
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense

noncomputable section
open TopologicalSpace MeasureTheory
open scoped Cardinal ENNReal

namespace PL1CD

def metricCode (E : Type) [MetricSpace E] [SeparableSpace E] [Nonempty E]
    (x : E) : ℕ → ℝ := fun n => dist x (denseSeq E n)

theorem metricCode_injective (E : Type) [MetricSpace E] [SeparableSpace E] [Nonempty E] :
    Function.Injective (metricCode E) := by
  intro x y h
  have heq : (fun z => dist x z) = fun z => dist y z :=
    (denseRange_denseSeq E).equalizer (continuous_const.dist continuous_id)
      (continuous_const.dist continuous_id) h
  have hzero : dist y x = 0 := by simpa using (congrFun heq x).symm
  exact (dist_eq_zero.mp hzero).symm

theorem separable_metric_cardinality_le_continuum
    (E : Type) [MetricSpace E] [SeparableSpace E] [Nonempty E] :
    Cardinal.mk E ≤ Cardinal.continuum := by
  have h := Cardinal.mk_le_of_injective (metricCode_injective E)
  simpa [Cardinal.mk_real] using h

def operatorCode (𝕜 E : Type) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeparableSpace E] (T : E →L[𝕜] E) : ℕ × ℕ → ℝ :=
  fun nm => dist (T (denseSeq E nm.1)) (denseSeq E nm.2)

theorem operatorCode_injective (𝕜 E : Type) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeparableSpace E] : Function.Injective (operatorCode 𝕜 E) := by
  intro T U h
  have hvalues : (fun n => T (denseSeq E n)) = fun n => U (denseSeq E n) := by
    funext n
    apply metricCode_injective E
    funext m
    exact congrFun h (n, m)
  have hfun : (T : E → E) = U :=
    (denseRange_denseSeq E).equalizer T.continuous U.continuous hvalues
  exact DFunLike.coe_injective hfun

theorem separable_operator_cardinality_le_continuum
    (𝕜 E : Type) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeparableSpace E] :
    Cardinal.mk (E →L[𝕜] E) ≤ Cardinal.continuum := by
  have h := Cardinal.mk_le_of_injective (operatorCode_injective 𝕜 E)
  simpa [Cardinal.mk_real] using h

theorem intervalL1_separableSpace (𝕜 : Type) [RCLike 𝕜] :
    SeparableSpace (PL1.IntervalL1 𝕜) := by
  let : SeparableSpace (Lp 𝕜 1 (volume : Measure unitInterval)) :=
    (ContinuousMap.toLp_denseRange 𝕜 (volume : Measure unitInterval) 𝕜
      (p := 1) (by norm_num)).separableSpace
      (ContinuousMap.toLp 1 (volume : Measure unitInterval) 𝕜).continuous
  exact (PL1.IntervalSubtype.equiv 𝕜).surjective.denseRange.separableSpace
    (PL1.IntervalSubtype.equiv 𝕜).continuous

theorem l1Operator_cardinality_le_continuum (𝕜 : Type) [RCLike 𝕜] :
    Cardinal.mk (L1Operator 𝕜) ≤ Cardinal.continuum := by
  let := intervalL1_separableSpace 𝕜
  exact separable_operator_cardinality_le_continuum 𝕜 (PL1.IntervalL1 𝕜)

theorem closedOperatorIdeals_cardinality_le (𝕜 : Type) [RCLike 𝕜] :
    Cardinal.mk (ClosedOperatorIdeals 𝕜) ≤ (2 : Cardinal) ^ Cardinal.continuum := by
  have hinj : Function.Injective (fun I : ClosedOperatorIdeals 𝕜 =>
      (I.val : Set (L1Operator 𝕜))) := by
    intro I J h
    apply Subtype.ext
    exact SetLike.coe_injective h
  calc
    Cardinal.mk (ClosedOperatorIdeals 𝕜) ≤ Cardinal.mk (Set (L1Operator 𝕜)) :=
      Cardinal.mk_le_of_injective hinj
    _ = (2 : Cardinal) ^ Cardinal.mk (L1Operator 𝕜) := Cardinal.mk_set
    _ ≤ (2 : Cardinal) ^ Cardinal.continuum :=
      Cardinal.power_le_power_left (by norm_num) (l1Operator_cardinality_le_continuum 𝕜)

end PL1CD
