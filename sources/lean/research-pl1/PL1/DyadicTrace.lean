import PL1.TraceBounds
import Mathlib.MeasureTheory.Function.Floor

/-! # Concrete dyadic traces on the reviewed interval L1 space

The dyadic index is clamped at the two ends. Thus the cells partition all of
the real line, while their restrictions to [0,1] are the usual dyadic intervals.
Outside values disappear in the reviewed restricted Lebesgue measure.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.DyadicTrace

theorem intervalMeasure_probability : IsProbabilityMeasure intervalMeasure := by
  constructor
  simp [intervalMeasure, Real.volume_Icc]

attribute [local instance] intervalMeasure_probability

def index (n : ℕ) (x : ℝ) : ℕ := min ⌊(2 : ℝ) ^ n * x⌋₊ (2 ^ n - 1)

theorem measurable_index (n : ℕ) : Measurable (index n) :=
  (Nat.measurable_floor.comp (measurable_const.mul measurable_id)).min measurable_const

theorem index_lt (n : ℕ) (x : ℝ) : index n x < 2 ^ n :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (pow_pos (by decide) n) (by decide))

def cell (n i : ℕ) : Set ℝ := {x | index n x = i}

theorem measurableSet_cell (n i : ℕ) : MeasurableSet (cell n i) :=
  (measurable_index n) (measurableSet_singleton i)

theorem pairwiseDisjoint_cell (n : ℕ) : Pairwise (fun i j => Disjoint (cell n i) (cell n j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact hij (hxi.symm.trans hxj)

theorem cover_cell (n : ℕ) : (⋃ i ∈ Finset.range (2 ^ n), cell n i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨index n x, Finset.mem_range.mpr (index_lt n x), rfl⟩

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The canonical restriction of an interval L1 operator to interval L-infinity. -/
def restrictLinfty (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) :
    Lp 𝕜 ∞ intervalMeasure →L[𝕜] IntervalL1 𝕜 :=
  R.comp (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)

def trace (n : ℕ) (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) : 𝕜 :=
  TraceBounds.partitionTrace intervalMeasure (cell n) (measurableSet_cell n)
    (Finset.range (2 ^ n)) R

theorem trace_eq (n : ℕ) (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) :
    trace n R = ∑ i ∈ Finset.range (2 ^ n), ∫ x in cell n i,
      R (indicatorConstLp 1 (measurableSet_cell n i)
        (measure_ne_top intervalMeasure (cell n i)) (1 : 𝕜)) x ∂intervalMeasure :=
  TraceBounds.partitionTrace_eq _ _ _ _ _

theorem norm_trace_le (n : ℕ) (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) :
    ‖trace n R‖ ≤ ‖restrictLinfty R‖ :=
  TraceBounds.norm_partitionTrace_le _ _ _ _ (pairwiseDisjoint_cell n) _

theorem trace_id (n : ℕ) : trace n (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜)) = 1 :=
  TraceBounds.partitionTrace_id _ _ _ _ (pairwiseDisjoint_cell n) (cover_cell n)

theorem one_le_norm_id_sub (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (hR : Tendsto (fun n => trace n R) atTop (𝓝 0)) :
    1 ≤ ‖restrictLinfty (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) - R)‖ :=
  TraceBounds.one_le_norm_id_sub_of_trace_tendsto_zero _ cell measurableSet_cell
    (fun n => Finset.range (2 ^ n)) pairwiseDisjoint_cell cover_cell R hR

theorem trace_tendsto_zero_of_approximation (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (T : ℕ → IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (hT : ∀ m, Tendsto (fun n => trace n (T m)) atTop (𝓝 0))
    (happrox : Tendsto (fun m => ‖restrictLinfty (R - T m)‖) atTop (𝓝 0)) :
    Tendsto (fun n => trace n R) atTop (𝓝 0) :=
  TraceBounds.trace_tendsto_zero_of_approximation _ cell measurableSet_cell
    (fun n => Finset.range (2 ^ n)) pairwiseDisjoint_cell R T hT happrox

end PL1.DyadicTrace
