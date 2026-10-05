import ThesisCommon.Analysis.BooleanStoneContinuousApproximation
import ThesisCommon.Analysis.BooleanStoneMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Sequences

/-! Continuous scalar functions are measurable for the sigma algebra generated
by the Stone clopens. This does not identify that sigma algebra with all Borel sets. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {B 𝕜 : Type*} [BooleanAlgebra B] [RCLike 𝕜]

theorem measurable_booleanStone_locallyConstant
    (g : C(BooleanStonePoint B, 𝕜)) (hg : IsLocallyConstant g) : Measurable g := by
  obtain ⟨s, a, ha⟩ := exists_booleanStone_sum_of_locallyConstant g hg
  have h : Measurable (fun p => ∑ c ∈ s,
      (booleanStoneSet (a c)).indicator (fun _ => c) p) :=
    Finset.measurable_sum s fun c _ => measurable_const.indicator (measurableSet_booleanStoneSet _)
  convert h using 1
  exact funext ha

theorem measurable_booleanStone_continuous (f : C(BooleanStonePoint B, 𝕜)) : Measurable f := by
  obtain ⟨g, hg, ht⟩ := mem_closure_iff_seq_limit.mp
    (dense_booleanStone_locallyConstant (B := B) (𝕜 := 𝕜) f)
  apply measurable_of_tendsto_metrizable (fun n => measurable_booleanStone_locallyConstant (g n) (hg n))
  apply tendsto_pi_nhds.mpr
  intro p
  exact (continuous_eval_const p).continuousAt.tendsto.comp ht

theorem stronglyMeasurable_booleanStone_continuous (f : C(BooleanStonePoint B, 𝕜)) :
    StronglyMeasurable f := (measurable_booleanStone_continuous f).stronglyMeasurable

theorem memLp_booleanStone_continuous (f : C(BooleanStonePoint B, 𝕜))
    (μ : Measure (BooleanStonePoint B)) [IsFiniteMeasure μ] (p : ℝ≥0∞) : MemLp f p μ :=
  MemLp.of_bound (stronglyMeasurable_booleanStone_continuous f).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

end ThesisCommon
