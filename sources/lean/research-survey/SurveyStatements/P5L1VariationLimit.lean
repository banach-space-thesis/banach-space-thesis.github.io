import SurveyStatements.P5L1VariationBound
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Actual bounded L¹ Haar multipliers have absolutely summable symbol
increments and a limit along every nested dyadic branch. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support
namespace DyadicBranch
variable {r : ℕ} (B : DyadicBranch r) (𝕜 : Type*) [RCLike 𝕜]
  (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
  (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
  (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
    D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)

include hD

theorem symbol_increments_summable :
    Summable (fun j => ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) :=
  summable_of_sum_range_le (fun _ => norm_nonneg _)
    (B.finite_variation_le 𝕜 D d hD)

theorem symbol_variation_tsum_le :
    (∑' j, ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) ≤ 6 * ‖D‖ :=
  (B.symbol_increments_summable 𝕜 D d hD).tsum_le_of_sum_range_le
    (B.finite_variation_le 𝕜 D d hD)

theorem symbol_cauchySeq : CauchySeq (B.symbol 𝕜 d) := by
  apply cauchySeq_of_summable_dist
  simpa only [dist_eq_norm, norm_sub_rev] using B.symbol_increments_summable 𝕜 D d hD

theorem symbol_exists_limit :
    ∃ c : 𝕜, Tendsto (B.symbol 𝕜 d) atTop (𝓝 c) :=
  cauchySeq_tendsto_of_complete (B.symbol_cauchySeq 𝕜 D d hD)

end DyadicBranch
end SurveyStatements.P5L1Variation
