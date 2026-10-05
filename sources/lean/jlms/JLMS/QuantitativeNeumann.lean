import JLMS.IdentityEssentialNorm
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Quantitative Neumann inversion

An operator at distance at most r<1 from the identity has an inverse of norm
at most 1/(1−r). The inverse is the actual Neumann series, whose powers are
dominated by the real geometric series. This retains the constants needed
for a sharp factorization from nearly diagonal norming matrices.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [Nontrivial E]

theorem exists_inverse_near_identity (F : E →L[𝕜] E) {r : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) (hclose : ‖ContinuousLinearMap.id 𝕜 E - F‖ ≤ r) :
    ∃ G : E →L[𝕜] E, G.comp F = ContinuousLinearMap.id 𝕜 E ∧ ‖G‖ ≤ 1 / (1 - r) := by
  let t : E →L[𝕜] E := 1 - F
  have ht : ‖t‖ < 1 := hclose.trans_lt hrone
  let u := Units.oneSub t ht
  let G : E →L[𝕜] E := ↑u⁻¹
  have hu : (u : E →L[𝕜] E) = F := by
    change 1 - (1 - F) = F
    abel
  refine ⟨G, ?_, ?_⟩
  · change (↑u⁻¹ : E →L[𝕜] E) * F = 1
    rw [← hu]
    exact u.inv_val
  · have hgeom : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr hrone
    have hpow (n : ℕ) : ‖t ^ n‖ ≤ r ^ n :=
      (norm_pow_le t n).trans (pow_le_pow_left₀ (norm_nonneg t) hclose n)
    have hs := hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) hpow
    change ‖∑' n : ℕ, t ^ n‖ ≤ 1 / (1 - r)
    calc
      _ ≤ ∑' n, ‖t ^ n‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ, r ^ n := hs.tsum_le_tsum hpow hgeom
      _ = 1 / (1 - r) := by
        rw [tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr]), one_div]

end JLMS
