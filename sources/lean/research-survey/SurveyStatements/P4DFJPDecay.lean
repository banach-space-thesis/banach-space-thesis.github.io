import SurveyStatements.P4DFJPGauge
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Decay of the concrete DFJP gauges on the generating set

The source uses all integer indices. Both tails must therefore be treated:
for positive indices use the `2^j K` summand; for negative indices use the
`2^-j B_E` summand and the original norm bound.
-/

noncomputable section

set_option autoImplicit false

open Set Metric
open scoped Pointwise

namespace SurveyStatements.P4

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

lemma dfjpGauge_le_of_mem {K : Set E} {x : E} (hx : x ∈ K) (j : ℤ) :
    dfjpGauge K j x ≤ (2 : ℝ) ^ (-j) := by
  have ha : 0 < (2 : ℝ) ^ j := zpow_pos two_pos _
  rw [dfjpGauge, zpow_neg]
  apply gauge_le_of_mem (inv_nonneg.mpr ha.le)
  refine ⟨((2 : ℝ) ^ j) • x, ?_, inv_smul_smul₀ ha.ne' x⟩
  have hz : (0 : E) ∈ ((2 : ℝ) ^ (-j)) • closedBall (0 : E) 1 :=
    ⟨0, by simp, smul_zero _⟩
  simpa [dfjpNeighborhood, paddedNeighborhood] using
    add_mem_add (smul_mem_smul_set hx) hz

lemma dfjpGauge_le_scale_mul_norm {K : Set E} (h0 : (0 : E) ∈ K)
    (j : ℤ) (x : E) : dfjpGauge K j x ≤ (2 : ℝ) ^ j * ‖x‖ := by
  simpa [zpow_neg, div_eq_mul_inv, mul_comm] using dfjpGauge_le_norm h0 j x

lemma dfjpGauge_sq_le_positive_tail {K : Set E} {x : E} (hx : x ∈ K) (n : ℕ) :
    (dfjpGauge K (n : ℤ) x) ^ 2 ≤ (1 / 4 : ℝ) ^ n := by
  calc
    (dfjpGauge K (n : ℤ) x) ^ 2 ≤ ((2 : ℝ) ^ (-(n : ℤ))) ^ 2 :=
      pow_le_pow_left₀ (dfjpGauge_nonneg _ _ _) (dfjpGauge_le_of_mem hx _) 2
    _ = (1 / 4 : ℝ) ^ n := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num

lemma dfjpGauge_sq_le_negative_tail {K : Set E} (h0 : (0 : E) ∈ K)
    (x : E) (n : ℕ) :
    (dfjpGauge K (-(n : ℤ)) x) ^ 2 ≤ ‖x‖ ^ 2 * (1 / 4 : ℝ) ^ n := by
  calc
    (dfjpGauge K (-(n : ℤ)) x) ^ 2 ≤ (((2 : ℝ) ^ (-(n : ℤ))) * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (dfjpGauge_nonneg _ _ _)
        (dfjpGauge_le_scale_mul_norm h0 _ x) 2
    _ = ‖x‖ ^ 2 * (1 / 4 : ℝ) ^ n := by
      rw [mul_pow, zpow_neg, zpow_natCast, ← inv_pow, ← pow_mul,
        mul_comm n 2, pow_mul]
      norm_num
      ring

/-- Both integer tails of the squared gauges are summable for every vector
of `K`, as required before putting `K` into the DFJP space. -/
lemma summable_dfjpGauge_sq_of_mem {K : Set E} (h0 : (0 : E) ∈ K)
    {x : E} (hx : x ∈ K) : Summable (fun j : ℤ => (dfjpGauge K j x) ^ 2) := by
  have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply Summable.of_nat_of_neg
  · exact hgeom.of_nonneg_of_le (fun _ => sq_nonneg _)
      (dfjpGauge_sq_le_positive_tail hx)
  · exact (hgeom.mul_left (‖x‖ ^ 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) (dfjpGauge_sq_le_negative_tail h0 x)

end SurveyStatements.P4
