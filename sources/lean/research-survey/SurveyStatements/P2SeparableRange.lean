import SurveyStatements.P2Definitions
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Sequences
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! The actual closed two-sided ideal of operators with separable range.
Compactness gives separability by covering the domain with countably many
closed balls. Operator-norm limits lie in the closed union of the old ranges. -/

noncomputable section
set_option autoImplicit false
open Filter Topology TopologicalSpace

namespace SurveyStatements.P2

universe v w z
variable {X : Type v} {Y : Type w} {Z : Type z}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- Compact operators have genuinely separable ranges, without a separability
assumption on their domain. -/
theorem compactOperator_range_isSeparable {T : X →L[ℂ] Y} (hT : IsCompactOperator T) :
    IsSeparable (Set.range T) := by
  have hs : ∀ n : ℕ, IsSeparable (T '' Metric.closedBall 0 (n : ℝ)) := by
    intro n
    exact (hT.isCompact_closure_image_closedBall (n : ℝ)).isSeparable.mono subset_closure
  apply (IsSeparable.iUnion hs).mono
  rintro y ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  exact Set.mem_iUnion.mpr ⟨n, x, by simpa [Metric.mem_closedBall, dist_zero_right] using hn, rfl⟩

theorem isSeparableRange_zero : IsSeparable (Set.range (0 : X →L[ℂ] Y)) := by
  change IsSeparable (Set.range (fun _ : X => (0 : Y)))
  simpa only [Set.range_const] using
    (Set.finite_singleton (0 : Y)).isSeparable

theorem isSeparableRange_add {S T : X →L[ℂ] Y}
    (hS : IsSeparable (Set.range S)) (hT : IsSeparable (Set.range T)) :
    IsSeparable (Set.range (S + T)) := by
  apply ((hS.prod hT).image (continuous_fst.add continuous_snd)).mono
  rintro y ⟨x, rfl⟩
  exact ⟨(S x, T x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩

theorem isSeparableRange_neg {T : X →L[ℂ] Y} (hT : IsSeparable (Set.range T)) :
    IsSeparable (Set.range (-T)) := by
  apply (hT.image continuous_neg).mono
  rintro y ⟨x, rfl⟩
  exact ⟨T x, ⟨x, rfl⟩, rfl⟩

theorem isSeparableRange_smul {T : X →L[ℂ] Y} (hT : IsSeparable (Set.range T)) (c : ℂ) :
    IsSeparable (Set.range (c • T)) := by
  apply (hT.image (continuous_const_smul c)).mono
  rintro y ⟨x, rfl⟩
  exact ⟨T x, ⟨x, rfl⟩, rfl⟩

theorem isSeparableRange_comp_left {T : X →L[ℂ] Y}
    (hT : IsSeparable (Set.range T)) (S : Y →L[ℂ] Z) :
    IsSeparable (Set.range (S.comp T)) := by
  apply (hT.image S.continuous).mono
  rintro y ⟨x, rfl⟩
  exact ⟨T x, ⟨x, rfl⟩, rfl⟩

theorem isSeparableRange_comp_right {T : Y →L[ℂ] Z}
    (hT : IsSeparable (Set.range T)) (S : X →L[ℂ] Y) :
    IsSeparable (Set.range (T.comp S)) := by
  apply hT.mono
  rintro y ⟨x, rfl⟩
  exact ⟨S x, rfl⟩

/-- Separable-range operators are closed in the actual operator norm. -/
theorem isClosed_setOf_isSeparableRange :
    IsClosed {T : X →L[ℂ] Y | IsSeparable (Set.range T)} := by
  apply IsSeqClosed.isClosed
  intro T S hT hlim
  have hs : IsSeparable (closure (⋃ n : ℕ, Set.range (T n))) :=
    (IsSeparable.iUnion hT).closure
  apply hs.mono
  rintro y ⟨x, rfl⟩
  apply isClosed_closure.mem_of_tendsto
    ((continuous_eval_const x).tendsto S |>.comp hlim)
  exact Filter.Eventually.of_forall fun n =>
    subset_closure (Set.mem_iUnion.mpr ⟨n, x, rfl⟩)

/-- The source's separable-range ideal uses the full operator range. -/
def SeparableRangeOperators (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] :
    TwoSidedIdeal (BoundedOperators X) :=
  TwoSidedIdeal.mk' {T | IsSeparable (Set.range T)}
    isSeparableRange_zero isSeparableRange_add isSeparableRange_neg
    (fun {S T} hT => isSeparableRange_comp_left hT S)
    (fun {S T} hS => isSeparableRange_comp_right hS T)

@[simp] theorem mem_separableRangeOperators (T : BoundedOperators X) :
    T ∈ SeparableRangeOperators X ↔ IsSeparable (Set.range T) := by
  simp [SeparableRangeOperators]

theorem separableRangeOperators_isClosed :
    IsClosed (SeparableRangeOperators X : Set (BoundedOperators X)) := by
  convert (isClosed_setOf_isSeparableRange (X := X) (Y := X)) using 1
  ext T
  simp

theorem compactOperators_subset_separableRangeOperators :
    (CompactOperators X : Set (BoundedOperators X)) ⊆ SeparableRangeOperators X := by
  intro T hT
  apply (mem_separableRangeOperators T).mpr
  exact compactOperator_range_isSeparable (T := T) hT

/-- The identity belongs exactly when the space itself is separable. -/
theorem one_mem_separableRangeOperators_iff :
    (1 : BoundedOperators X) ∈ SeparableRangeOperators X ↔ SeparableSpace X := by
  rw [mem_separableRangeOperators]
  change IsSeparable (Set.range (fun x : X => x)) ↔ SeparableSpace X
  rw [Set.range_eq_univ.mpr (show Function.Surjective (fun x : X => x) from
    fun x => ⟨x, rfl⟩)]
  exact isSeparable_univ_iff

theorem separableRangeOperators_ne_top (hX : ¬ SeparableSpace X) :
    SeparableRangeOperators X ≠ ⊤ := by
  intro htop
  exact hX (one_mem_separableRangeOperators_iff.mp
    ((SeparableRangeOperators X).one_mem htop))

end SurveyStatements.P2
