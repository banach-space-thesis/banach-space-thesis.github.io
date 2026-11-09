import ThesisCommon.Analysis.SchauderOperators
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Summable matrix errors on a Schauder basis. All diagonal operators here
are already bounded maps or norm-convergent rank-one series; no bounded
multiplier is inferred merely from bounded coefficients. -/

noncomputable section
open scoped BigOperators
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]
variable (b : NormalizedSchauderBasis 𝕜 X)

def summableMatrixTerm (a : ℕ × ℕ → 𝕜) (ij : ℕ × ℕ) : X →L[𝕜] X :=
  (b.coord ij.2).smulRight (a ij • b.vector ij.1)

theorem norm_summableMatrixTerm_le {K : ℝ} (hK : ∀ n, ‖b.coord n‖ ≤ K)
    (a : ℕ × ℕ → 𝕜) (ij : ℕ × ℕ) :
    ‖b.summableMatrixTerm a ij‖ ≤ K * ‖a ij‖ := by
  rw [summableMatrixTerm, ContinuousLinearMap.norm_smulRight_apply, norm_smul,
    b.norm_vector, mul_one]
  exact mul_le_mul_of_nonneg_right (hK ij.2) (norm_nonneg _)

theorem summable_matrixTerms {K : ℝ} (hK : ∀ n, ‖b.coord n‖ ≤ K)
    (a : ℕ × ℕ → 𝕜) (ha : Summable (fun ij => ‖a ij‖)) :
    Summable (b.summableMatrixTerm a) :=
  (ha.mul_left K).of_norm_bounded (b.norm_summableMatrixTerm_le hK a)

def summableMatrix (a : ℕ × ℕ → 𝕜) : X →L[𝕜] X :=
  ∑' ij, b.summableMatrixTerm a ij

theorem norm_summableMatrix_le {K : ℝ} (hK : ∀ n, ‖b.coord n‖ ≤ K)
    (a : ℕ × ℕ → 𝕜) (ha : Summable (fun ij => ‖a ij‖)) :
    ‖b.summableMatrix a‖ ≤ K * ∑' ij, ‖a ij‖ := by
  have hn : Summable (fun ij => ‖b.summableMatrixTerm a ij‖) :=
    (ha.mul_left K).of_nonneg_of_le (fun ij => norm_nonneg _)
      (b.norm_summableMatrixTerm_le hK a)
  calc
    _ ≤ ∑' ij, ‖b.summableMatrixTerm a ij‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' ij, K * ‖a ij‖ := hn.tsum_le_tsum
      (b.norm_summableMatrixTerm_le hK a) (ha.mul_left K)
    _ = _ := tsum_mul_left

theorem summableMatrix_entry {K : ℝ} (hK : ∀ n, ‖b.coord n‖ ≤ K)
    (a : ℕ × ℕ → 𝕜) (ha : Summable (fun ij => ‖a ij‖)) (i j : ℕ) :
    b.coord i (b.summableMatrix a (b.vector j)) = a (i, j) := by
  let ev := (b.coord i).comp (ContinuousLinearMap.apply 𝕜 X (b.vector j))
  change ev (∑' ij, b.summableMatrixTerm a ij) = _
  rw [ev.map_tsum (b.summable_matrixTerms hK a ha), tsum_eq_single (i, j)]
  · simp [ev, summableMatrixTerm, b.biorthogonal]
  · intro ij hij
    rcases ij with ⟨r, s⟩
    have hne : r ≠ i ∨ s ≠ j := by
      by_contra hn
      push_neg at hn
      exact hij (Prod.ext hn.1 hn.2)
    rcases hne with hr | hs
    · simp [ev, summableMatrixTerm, b.biorthogonal, apply_ite, hr.symm]
    · simp [ev, summableMatrixTerm, b.biorthogonal, hs]

/-- Zero off-diagonal matrix coefficients imply an actual diagonal action. -/
theorem diagonal_action_of_entries (D : X →L[𝕜] X)
    (hD : ∀ i j, i ≠ j → b.coord i (D (b.vector j)) = 0) (j : ℕ) :
    D (b.vector j) = b.coord j (D (b.vector j)) • b.vector j := by
  apply b.ext
  intro i
  rw [map_smul, b.biorthogonal]
  by_cases hij : i = j
  · subst i; simp
  · simp [hij, hD i j hij]

/-- Subtract the absolutely summable off-diagonal part. The resulting
bounded operator has exactly the original diagonal. -/
theorem subtract_offDiagonal_action {K : ℝ} (hK : ∀ n, ‖b.coord n‖ ≤ K)
    (S : X →L[𝕜] X)
    (ha : Summable (fun ij : ℕ × ℕ =>
      ‖if ij.1 = ij.2 then (0 : 𝕜) else b.coord ij.1 (S (b.vector ij.2))‖))
    (j : ℕ) :
    (S - b.summableMatrix (fun ij =>
      if ij.1 = ij.2 then 0 else b.coord ij.1 (S (b.vector ij.2)))) (b.vector j) =
      b.coord j (S (b.vector j)) • b.vector j := by
  let a : ℕ × ℕ → 𝕜 := fun ij =>
    if ij.1 = ij.2 then 0 else b.coord ij.1 (S (b.vector ij.2))
  have he (i j : ℕ) : b.coord i ((S - b.summableMatrix a) (b.vector j)) =
      if i = j then b.coord j (S (b.vector j)) else 0 := by
    rw [ContinuousLinearMap.sub_apply, map_sub, b.summableMatrix_entry hK a ha]
    simp only [a]
    split_ifs with hij
    · subst i; simp
    · simp
  have hd := b.diagonal_action_of_entries (S - b.summableMatrix a)
    (fun i j hij => by rw [he, if_neg hij]) j
  simpa only [he, if_pos rfl] using hd

end ThesisCommon.NormalizedSchauderBasis
