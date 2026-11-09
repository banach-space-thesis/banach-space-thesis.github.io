import ThesisCommon.Analysis.LpHaarEdgeVariation
import ThesisCommon.Analysis.LpHaarSequentialGeometry
import Mathlib.Analysis.SpecificLimits.Normed

/-! A summable quantitative budget for trace balancing along the binary
tree. Child errors include the parent's inherited error; the estimate
controls edge differences rather than all distances from the root. -/

noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lpHaarHeapIndex_injective :
    Function.Injective (fun i : LpHaarTreeIndex => lpHaarHeapIndex i.1 i.2) := by
  rintro ⟨n, k⟩ ⟨m, l⟩ h
  have hn : 0 < 2 ^ n := pow_pos (by decide) _
  have hm : 0 < 2 ^ m := pow_pos (by decide) _
  have he : lpHaarEncode (some ⟨n, k⟩) = lpHaarEncode (some ⟨m, l⟩) := by
    simp only [lpHaarEncode, lpHaarHeapIndex] at h ⊢
    omega
  exact Option.some.inj (lpHaarEncode_injective he)

theorem lpHaarHeapIndex_parent (n : ℕ) (k : Fin (2 ^ (n + 1))) :
    lpHaarHeapIndex n (lpHaarParentIndex n k) = (lpHaarHeapIndex (n + 1) k - 1) / 2 := by
  change 2 ^ n + k.val / 2 - 1 = (2 ^ (n + 1) + k.val - 1 - 1) / 2
  have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  omega

def lpHaarTraceErrorBudget (δ : ℝ) (j : ℕ) : ℝ := δ * (1 / 2 : ℝ) ^ (2 * j + 2)

theorem lpHaarTraceErrorBudget_le {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) :
    lpHaarTraceErrorBudget δ j ≤ δ * (1 / 2 : ℝ) ^ j := by
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : j ≤ 2 * j + 2)) hδ

theorem lpHaarTraceErrorBudget_parent_le {δ : ℝ} (hδ : 0 ≤ δ) {j : ℕ} (hj : j ≠ 0) :
    lpHaarTraceErrorBudget δ ((j - 1) / 2) ≤ δ * (1 / 2 : ℝ) ^ j := by
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by omega : j ≤ 2 * ((j - 1) / 2) + 2)) hδ

theorem lpHaar_geometric_edge_budget (g t : ℕ → 𝕜) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ j, ‖g j - t j‖ ≤ lpHaarTraceErrorBudget δ j)
    (ht : ∀ j, j ≠ 0 → ‖t j - t ((j - 1) / 2)‖ ≤
      lpHaarTraceErrorBudget δ ((j - 1) / 2)) :
    let d : LpHaarTreeIndex → 𝕜 := fun i => g (lpHaarHeapIndex i.1 i.2)
    Summable (fun i => ‖lpHaarEdgeDifference d (t 0) i‖) ∧
      (∑' i, ‖lpHaarEdgeDifference d (t 0) i‖) ≤ 6 * δ := by
  intro d
  let u (j : ℕ) : ℝ := (3 * δ) * (1 / 2 : ℝ) ^ j
  have hu : Summable u :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (3 * δ)
  have hbound (i : LpHaarTreeIndex) : ‖lpHaarEdgeDifference d (t 0) i‖ ≤
      u (lpHaarHeapIndex i.1 i.2) := by
    rcases i with ⟨n, k⟩
    cases n with
    | zero =>
        simp only [lpHaarEdgeDifference, d, lpHaarHeapIndex_zero]
        have h := (hg 0).trans (lpHaarTraceErrorBudget_le hδ 0)
        simp only [pow_zero, mul_one] at h
        change ‖g 0 - t 0‖ ≤ u 0
        simp only [u, pow_zero, mul_one]
        linarith
    | succ n =>
        let j := lpHaarHeapIndex (n + 1) k
        have hj : j ≠ 0 := by
          have h := lpHaarHeapIndex_depth_le (n + 1) k
          change n + 1 ≤ j at h
          omega
        change ‖g j - g (lpHaarHeapIndex n (lpHaarParentIndex n k))‖ ≤ u j
        rw [lpHaarHeapIndex_parent]
        have htri : ‖g j - g ((j - 1) / 2)‖ ≤
            ‖g j - t j‖ + ‖t j - t ((j - 1) / 2)‖ + ‖t ((j - 1) / 2) - g ((j - 1) / 2)‖ := by
          simpa only [dist_eq_norm] using dist_triangle4 (g j) (t j) (t ((j - 1) / 2))
            (g ((j - 1) / 2))
        rw [norm_sub_rev (t ((j - 1) / 2))] at htri
        have h1 := (hg j).trans (lpHaarTraceErrorBudget_le hδ j)
        have h2 := (ht j hj).trans (lpHaarTraceErrorBudget_parent_le hδ hj)
        have h3 := (hg ((j - 1) / 2)).trans (lpHaarTraceErrorBudget_parent_le hδ hj)
        dsimp only [u]
        nlinarith
  have hs : Summable (fun i => ‖lpHaarEdgeDifference d (t 0) i‖) :=
    (hu.comp_injective lpHaarHeapIndex_injective).of_nonneg_of_le
      (fun i => norm_nonneg _) hbound
  refine ⟨hs, ?_⟩
  have hsum := hs.tsum_le_tsum_of_inj (fun i : LpHaarTreeIndex => lpHaarHeapIndex i.1 i.2)
    lpHaarHeapIndex_injective (fun j _ => by dsimp only [u]; positivity) hbound hu
  have huv : (∑' j, u j) = 6 * δ := by
    change (∑' j, (3 * δ) * (1 / 2 : ℝ) ^ j) = _
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
    ring
  exact hsum.trans_eq huv

end ThesisCommon
