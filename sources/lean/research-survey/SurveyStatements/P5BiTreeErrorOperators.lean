import SurveyStatements.P5GridCoordinateIncrements
import SurveyStatements.P5MixedDyadicPieces

/-! Bounded error operators built from actual grid increments and rectangular
conditional-expectation pieces. Their series require precisely the displayed
summable numerical budgets. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open BiTree
attribute [local irreducible] diagonalGrid superdiagonalGrid symbolGrid
  mixedLowerStrip mixedUpperStrip
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_comp_le_of_four_bounds {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A B : X →L[𝕜] X) {b : ℝ} (hb : 0 ≤ b)
    (hA : ‖A‖ ≤ b) (hB : ‖B‖ ≤ 4) : ‖A.comp B‖ ≤ b * 4 :=
  (A.opNorm_comp_le B).trans (mul_le_mul hA hB (norm_nonneg B) hb)

def lowerDiagonalErrorTerm (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (k : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  ∑ j ∈ Finset.range (k + 1),
    (diagonalGrid (p := p) d k - diagonalGrid (p := p) d (k + 1)).comp (mixedLowerStrip (𝕜 := 𝕜) (p := p) hp j j)

def lowerCoordinateErrorTerm (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (k : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  ∑ j ∈ Finset.range (k + 1),
    (symbolGrid (p := p) d (k + 1) j - symbolGrid (p := p) d k j).comp (mixedLowerStrip (𝕜 := 𝕜) (p := p) hp (k + 1) j)

def upperDiagonalErrorTerm (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (k : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  ∑ i ∈ Finset.range (k + 1),
    (superdiagonalGrid (p := p) d k - superdiagonalGrid (p := p) d (k + 1)).comp
      (mixedUpperStrip (𝕜 := 𝕜) (p := p) hp i (i + 1))

def upperCoordinateErrorTerm (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (k : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  ∑ i ∈ Finset.range k,
    (symbolGrid (p := p) d i (k + 1) - symbolGrid (p := p) d i k).comp (mixedUpperStrip (𝕜 := 𝕜) (p := p) hp i (k + 1))

theorem norm_lowerDiagonalErrorTerm_le (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j) (k : ℕ) :
    ‖lowerDiagonalErrorTerm (p := p) hp d k‖ ≤ 4 * (k + 1 : ℕ) * η k k := by
  have hgrid : ‖diagonalGrid (p := p) d k - diagonalGrid (p := p) d (k + 1)‖ ≤ η k k := by
    rw [norm_sub_rev]
    exact norm_diagonalGrid_step_le d η hs (fun n => hη n n) k
  unfold lowerDiagonalErrorTerm
  calc
    ‖∑ j ∈ Finset.range (k + 1),
        (diagonalGrid (p := p) d k - diagonalGrid (p := p) d (k + 1)).comp (mixedLowerStrip (𝕜 := 𝕜) (p := p) hp j j)‖ ≤
        ∑ j ∈ Finset.range (k + 1),
          ‖(diagonalGrid (p := p) d k - diagonalGrid (p := p) d (k + 1)).comp (mixedLowerStrip (𝕜 := 𝕜) (p := p) hp j j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (k + 1), η k k * 4 := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_comp_le_of_four_bounds
        (diagonalGrid (p := p) d k - diagonalGrid (p := p) d (k + 1))
        (mixedLowerStrip (𝕜 := 𝕜) hp j j) (hη k k) hgrid
        (norm_mixedLowerStrip_le (𝕜 := 𝕜) hp j j)
    _ = 4 * (k + 1 : ℕ) * η k k := by simp; ring

theorem norm_lowerCoordinateErrorTerm_le (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j) (k : ℕ) :
    ‖lowerCoordinateErrorTerm (p := p) hp d k‖ ≤ 4 * ∑ j ∈ Finset.range (k + 1), η k j := by
  unfold lowerCoordinateErrorTerm
  calc
    ‖∑ j ∈ Finset.range (k + 1),
        (symbolGrid (p := p) d (k + 1) j - symbolGrid (p := p) d k j).comp (mixedLowerStrip (𝕜 := 𝕜) (p := p) hp (k + 1) j)‖ ≤
        ∑ j ∈ Finset.range (k + 1),
          ‖(symbolGrid (p := p) d (k + 1) j - symbolGrid (p := p) d k j).comp (mixedLowerStrip (𝕜 := 𝕜) (p := p) hp (k + 1) j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1), η k j * 4 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hgrid : ‖symbolGrid (p := p) d (k + 1) j - symbolGrid (p := p) d k j‖ ≤ η k j :=
        norm_symbolGrid_outer_step_le (p := p) d η hs k j hjle (hη k j)
      exact norm_comp_le_of_four_bounds
        (symbolGrid (p := p) d (k + 1) j - symbolGrid (p := p) d k j)
        (mixedLowerStrip (𝕜 := 𝕜) hp (k + 1) j) (hη k j) hgrid
        (norm_mixedLowerStrip_le (𝕜 := 𝕜) hp (k + 1) j)
    _ = 4 * ∑ j ∈ Finset.range (k + 1), η k j := by rw [← Finset.sum_mul]; ring

theorem norm_upperDiagonalErrorTerm_le (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j) (k : ℕ) :
    ‖upperDiagonalErrorTerm (p := p) hp d k‖ ≤ 4 * (k + 1 : ℕ) * η k (k + 1) := by
  have hgrid : ‖superdiagonalGrid (p := p) d k - superdiagonalGrid (p := p) d (k + 1)‖ ≤
      η k (k + 1) := by
    rw [norm_sub_rev]
    exact norm_superdiagonalGrid_step_le d η hs (fun n => hη n (n + 1)) k
  unfold upperDiagonalErrorTerm
  calc
    ‖∑ i ∈ Finset.range (k + 1),
        (superdiagonalGrid (p := p) d k - superdiagonalGrid (p := p) d (k + 1)).comp
          (mixedUpperStrip (𝕜 := 𝕜) (p := p) hp i (i + 1))‖ ≤
        ∑ i ∈ Finset.range (k + 1),
          ‖(superdiagonalGrid (p := p) d k - superdiagonalGrid (p := p) d (k + 1)).comp
            (mixedUpperStrip (𝕜 := 𝕜) (p := p) hp i (i + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (k + 1), η k (k + 1) * 4 := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_comp_le_of_four_bounds
        (superdiagonalGrid (p := p) d k - superdiagonalGrid (p := p) d (k + 1))
        (mixedUpperStrip (𝕜 := 𝕜) hp i (i + 1)) (hη k (k + 1)) hgrid
        (norm_mixedUpperStrip_le (𝕜 := 𝕜) hp i (i + 1))
    _ = 4 * (k + 1 : ℕ) * η k (k + 1) := by simp; ring

theorem norm_upperCoordinateErrorTerm_le (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j) (k : ℕ) :
    ‖upperCoordinateErrorTerm (p := p) hp d k‖ ≤ 4 * ∑ i ∈ Finset.range k, η i k := by
  unfold upperCoordinateErrorTerm
  calc
    ‖∑ i ∈ Finset.range k,
        (symbolGrid (p := p) d i (k + 1) - symbolGrid (p := p) d i k).comp (mixedUpperStrip (𝕜 := 𝕜) (p := p) hp i (k + 1))‖ ≤
        ∑ i ∈ Finset.range k,
          ‖(symbolGrid (p := p) d i (k + 1) - symbolGrid (p := p) d i k).comp (mixedUpperStrip (𝕜 := 𝕜) (p := p) hp i (k + 1))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range k, η i k * 4 := by
      apply Finset.sum_le_sum
      intro i hi
      have hgrid : ‖symbolGrid (p := p) d i (k + 1) - symbolGrid (p := p) d i k‖ ≤ η i k :=
        norm_symbolGrid_inner_step_le (p := p) d η hs i k (Finset.mem_range.mp hi) (hη i k)
      exact norm_comp_le_of_four_bounds
        (symbolGrid (p := p) d i (k + 1) - symbolGrid (p := p) d i k)
        (mixedUpperStrip (𝕜 := 𝕜) hp i (k + 1)) (hη i k) hgrid
        (norm_mixedUpperStrip_le (𝕜 := 𝕜) hp i (k + 1))
    _ = 4 * ∑ i ∈ Finset.range k, η i k := by rw [← Finset.sum_mul]; ring

end SurveyStatements.P5

