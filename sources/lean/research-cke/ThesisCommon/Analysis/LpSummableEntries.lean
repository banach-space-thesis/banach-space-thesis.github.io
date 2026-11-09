import ThesisCommon.Analysis.SequenceEntryOperators
import ThesisCommon.Analysis.SequenceBlockTailBounds
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Absolutely summable matrix entries define an actual bounded operator
on lp for every p >= 1. This constructs the error operators in LPCK. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def lpElementaryOperator (p : ℝ≥0∞) [Fact (1 ≤ p)] (i j : ℕ) (A : X →L[𝕜] X) :
    lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p :=
  (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p i).comp (A.comp (lpCoordinate p j))

theorem norm_lpElementaryOperator_le (i j : ℕ) (A : X →L[𝕜] X) :
    ‖lpElementaryOperator p i j A‖ ≤ ‖A‖ :=
  (norm_comp_left_contraction _ (norm_lpSingleCLM_le i) _).trans
    (norm_comp_right_contraction _ _ (norm_lpCoordinate_le p j))

@[simp] theorem lpElementaryOperator_apply (i j : ℕ) (A : X →L[𝕜] X)
    (x : lp (fun _ : ℕ => X) p) (k : ℕ) :
    lpElementaryOperator p i j A x k = if k = i then A (x j) else 0 := by
  simp [lpElementaryOperator, lp.single_apply, Pi.single_apply]

variable [CompleteSpace X] {ι : Type*}

theorem lpElementaryOperator_summable (row col : ι → ℕ) (A : ι → X →L[𝕜] X)
    (hA : Summable (fun a => ‖A a‖)) :
    Summable (fun a => lpElementaryOperator p (row a) (col a) (A a)) :=
  hA.of_norm_bounded (fun a => norm_lpElementaryOperator_le (row a) (col a) (A a))

def lpSummableEntries (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (row col : ι → ℕ) (A : ι → X →L[𝕜] X) :
    lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p :=
  ∑' a, lpElementaryOperator p (row a) (col a) (A a)

omit [CompleteSpace X] in
theorem norm_lpSummableEntries_le (row col : ι → ℕ) (A : ι → X →L[𝕜] X)
    (hA : Summable (fun a => ‖A a‖)) : ‖lpSummableEntries p row col A‖ ≤ ∑' a, ‖A a‖ := by
  have hs : Summable (fun a => ‖lpElementaryOperator p (row a) (col a) (A a)‖) :=
    hA.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => norm_lpElementaryOperator_le _ _ _)
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum
    (fun a => norm_lpElementaryOperator_le _ _ _) hA)

theorem lpSummableEntries_apply (row col : ι → ℕ) (A : ι → X →L[𝕜] X)
    (hA : Summable (fun a => ‖A a‖)) (x : lp (fun _ : ℕ => X) p) (k : ℕ) :
    lpSummableEntries p row col A x k =
      ∑' a, if k = row a then A a (x (col a)) else 0 := by
  let ev : (lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) →L[𝕜] X :=
    (lpCoordinate p k).comp (ContinuousLinearMap.apply 𝕜 (lp (fun _ : ℕ => X) p) x)
  have hs := lpElementaryOperator_summable (p := p) row col A hA
  change ev (∑' a, lpElementaryOperator p (row a) (col a) (A a)) = _
  rw [ev.map_tsum hs]
  apply tsum_congr
  intro a
  exact lpElementaryOperator_apply _ _ _ _ _

end ThesisCommon
