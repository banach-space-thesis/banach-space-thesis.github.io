import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-! A finite measure has vanishing mass in shrinking punctured balls. -/
noncomputable section
open Filter Topology MeasureTheory
namespace ThesisCommon
variable {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]

theorem puncturedBalls_antitone (t : K) :
    Antitone (fun n : ℕ => Metric.ball t (1 / (n + 1 : ℝ)) \ {t}) := by
  intro m n hmn
  apply Set.diff_subset_diff_left
  apply Metric.ball_subset_ball
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

theorem iInter_puncturedBalls (t : K) :
    (⋂ n : ℕ, Metric.ball t (1 / (n + 1 : ℝ)) \ {t}) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := Set.mem_iInter.mp hx
  have hd : dist x t ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall fun n => (hx' n).1.le)
  exact (hx' 0).2 (Set.mem_singleton_iff.mpr (dist_eq_zero.mp (le_antisymm hd dist_nonneg)))

theorem tendsto_measure_puncturedBalls (ν : Measure K) [IsFiniteMeasure ν] (t : K) :
    Tendsto (fun n : ℕ => ν (Metric.ball t (1 / (n + 1 : ℝ)) \ {t})) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun n : ℕ => (measurableSet_ball.diff (measurableSet_singleton t)).nullMeasurableSet)
    (puncturedBalls_antitone t) ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, iInter_puncturedBalls, measure_empty] using h

theorem tendsto_measureReal_puncturedBalls (ν : Measure K) [IsFiniteMeasure ν] (t : K) :
    Tendsto (fun n : ℕ => ν.real (Metric.ball t (1 / (n + 1 : ℝ)) \ {t})) atTop (𝓝 0) := by
  simpa only [ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp
      (tendsto_measure_puncturedBalls ν t)

end ThesisCommon
