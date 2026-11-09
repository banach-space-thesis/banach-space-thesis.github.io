import SurveyStatements.P5L1VariationTreeCoordinates
import SurveyStatements.P5L1VariationLocalTree

/-! Conjugating a finite operator by an actual tree permutation merely
permutes its Haar diagonal. The signs in the primal and dual cancel. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem nodeAction_inv_apply {M : ℕ} (σ : DyadicTreePerm M)
    (n : ℕ) (hn : n ≤ M) (k : Fin (2 ^ n)) :
    nodeAction σ⁻¹ n hn (nodeAction σ n hn k) = k := by
  have h := nodeAction_mul σ⁻¹ σ n hn k
  rw [inv_mul_cancel, nodeAction_one] at h
  exact h.symm

def haarOperatorDiagonal (𝕜 : Type*) [RCLike 𝕜]
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (n : ℕ) (k : Fin (2 ^ n)) : 𝕜 :=
  lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k (R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k))

theorem terminalConjugate_diagonal (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n + 1 ≤ M) (σ : DyadicTreePerm M)
    (R : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (k : Fin (2 ^ n)) :
    lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k
      (terminalPermutation 𝕜 M (σ⁻¹).val
        (R (terminalPermutation 𝕜 M σ.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)))) =
      haarOperatorDiagonal 𝕜 R n (nodeAction σ n (by omega) k) := by
  have hi : terminalPermutation 𝕜 M (σ⁻¹).val
      (terminalPermutation 𝕜 M σ.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)) =
        lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
    have h := congrArg (fun L : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 =>
      L (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)) (terminalPermutation_inverse 𝕜 M σ.val)
    simpa only [ContinuousLinearMap.comp_apply,
      lpHaarDyadicMean_fix_earlier_haar 𝕜 ⟨1, le_rfl⟩ (by norm_num) n M k k.isLt (by omega)] using h
  rcases terminalPermutation_haar_signed 𝕜 M n hn σ k with hp | hp
  · have hvinv : terminalPermutation 𝕜 M (σ⁻¹).val
        (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k)) =
          lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
      rw [hp] at hi
      exact hi
    have hc := terminalPermutation_coordinate_of_signed_haar 𝕜 M n hn σ⁻¹
      (nodeAction σ n (by omega) k) 1
      (by simpa only [nodeAction_inv_apply, one_smul] using hvinv)
      (R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k)))
    rw [hp]
    simpa only [nodeAction_inv_apply, one_mul, haarOperatorDiagonal] using hc
  · have hvinv : terminalPermutation 𝕜 M (σ⁻¹).val
        (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k)) =
          -lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
      rw [hp, map_neg] at hi
      exact neg_eq_iff_eq_neg.mp hi
    have hc := terminalPermutation_coordinate_of_signed_haar 𝕜 M n hn σ⁻¹
      (nodeAction σ n (by omega) k) (-1)
      (by simpa only [nodeAction_inv_apply, neg_one_smul] using hvinv)
      (R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k)))
    rw [hp, map_neg, map_neg, map_neg]
    simpa only [nodeAction_inv_apply, neg_one_mul, haarOperatorDiagonal, neg_neg] using congrArg Neg.neg hc

theorem localFiniteReynolds_diagonal_apply (𝕜 : Type*) [RCLike 𝕜]
    (M n r : ℕ) (hn : n + 1 ≤ M) (hr : r ≤ M) (root : Fin (2 ^ r))
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (k : Fin (2 ^ n)) :
    haarOperatorDiagonal 𝕜 (localFiniteReynolds 𝕜 M r hr root R) n k =
      (Fintype.card (LocalDyadicTreePerm M r hr root) : 𝕜)⁻¹ *
        ∑ g : LocalDyadicTreePerm M r hr root,
          haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n (nodeAction g.val n (by omega) k) := by
  rw [haarOperatorDiagonal, localFiniteReynolds, terminalReynolds_apply, map_smul, map_sum,
    smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  exact terminalConjugate_diagonal 𝕜 M n hn g.val (extendMeanZero 𝕜 R) k

end SurveyStatements.P5L1Variation
