import SurveyStatements.P5L1VariationLocalLevelAverage
import SurveyStatements.P5L1VariationTraceFromFinite

/-! Full-sequence convergence of the local level-averaged Haar diagonal
of an arbitrary bounded operator on the actual mean-zero L¹ space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

def leftDyadicBranch (r : ℕ) (root : Fin (2 ^ r)) : DyadicBranch r where
  index j := ⟨root.val * 2 ^ j, by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right root.isLt (by positivity)⟩
  parent j := by
    apply Fin.ext
    change (root.val * 2 ^ (j + 1)) / 2 = root.val * 2 ^ j
    rw [pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by omega)]

theorem leftDyadicBranch_root_prefix (r : ℕ) (root : Fin (2 ^ r)) (j : ℕ) :
    prefixIndex (r + j) r (by omega) ((leftDyadicBranch r root).index j) = root := by
  apply Fin.ext
  change (root.val * 2 ^ j) / 2 ^ ((r + j) - r) = root.val
  rw [Nat.add_sub_cancel_left]
  exact Nat.mul_div_cancel root.val (by positivity)

theorem localLevelAverage_finite_eigenoperators (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r))
    (N : ℕ) :
    ∃ D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜, ‖D‖ ≤ 2 * ‖R‖ ∧
      ∀ j < N + 1,
        D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) ((leftDyadicBranch r root).index j)) =
          localLevelAverage 𝕜 R (r + j) r (by omega) root •
            lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) ((leftDyadicBranch r root).index j) := by
  refine ⟨localFiniteReynolds 𝕜 (r + N + 1) r (by omega) root R,
    localFiniteReynolds_norm_le 𝕜 _ _ _ root R, ?_⟩
  intro j hj
  exact localFiniteReynolds_haar_average 𝕜 (r + N + 1) (r + j) r (by omega)
    (by omega) root R ((leftDyadicBranch r root).index j) (leftDyadicBranch_root_prefix r root j)

theorem arbitrary_operator_local_average_limit (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r)) :
    Summable (fun j => ‖localLevelAverage 𝕜 R (r + (j + 1)) r (by omega) root -
      localLevelAverage 𝕜 R (r + j) r (by omega) root‖) ∧
      (∑' j, ‖localLevelAverage 𝕜 R (r + (j + 1)) r (by omega) root -
        localLevelAverage 𝕜 R (r + j) r (by omega) root‖) ≤ 12 * ‖R‖ ∧
      ∃ c : 𝕜, ‖c‖ ≤ 2 * ‖R‖ ∧
        Tendsto (fun j => localLevelAverage 𝕜 R (r + j) r (by omega) root) atTop (𝓝 c) := by
  have h := exists_limit_of_finite_branch_eigenoperators 𝕜 (leftDyadicBranch r root)
    (fun j => localLevelAverage 𝕜 R (r + j) r (by omega) root) (2 * ‖R‖)
    (localLevelAverage_finite_eigenoperators 𝕜 R r root)
  convert h using 1 <;> ring

end SurveyStatements.P5L1Variation
