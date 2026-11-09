import SurveyStatements.P4Definitions
import Mathlib.Analysis.Convex.Gauge

/-!
# The concrete gauges in the DFJP construction

The neighborhoods and gauges here are those of source
`p5:thm:dfjp-interpolation`: `U_j = 2^j K + 2^(-j) B_E`, with `j : ℤ`.
This module proves their elementary norm comparison and decay estimates.
It does not assume the DFJP factorization conclusion.
-/

noncomputable section

set_option autoImplicit false

open Set Metric Filter Topology
open scoped Pointwise

namespace SurveyStatements.P4

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The two summands in a DFJP neighborhood, allowing arbitrary positive scales. -/
def paddedNeighborhood (K : Set E) (a b : ℝ) : Set E :=
  a • K + b • closedBall (0 : E) 1

/-- The actual integer-indexed neighborhoods in the paper. -/
def dfjpNeighborhood (K : Set E) (j : ℤ) : Set E :=
  paddedNeighborhood K ((2 : ℝ) ^ j) ((2 : ℝ) ^ (-j))

/-- Its real-valued Minkowski functional. -/
def dfjpGauge (K : Set E) (j : ℤ) (x : E) : ℝ :=
  gauge (dfjpNeighborhood K j) x

lemma closedBall_subset_paddedNeighborhood {K : Set E} (h0 : (0 : E) ∈ K)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    closedBall (0 : E) b ⊆ paddedNeighborhood K a b := by
  have hball : b • closedBall (0 : E) 1 = closedBall (0 : E) b := by
    simpa [Real.norm_of_nonneg hb.le] using
      (smul_closedBall' hb.ne' (0 : E) (1 : ℝ))
  intro x hx
  have hzero : (0 : E) ∈ a • K := ⟨0, h0, smul_zero a⟩
  have hx' : x ∈ b • closedBall (0 : E) 1 := hball.symm ▸ hx
  simpa [paddedNeighborhood] using add_mem_add hzero hx'

lemma paddedNeighborhood_subset_closedBall {K : Set E} {M a b : ℝ}
    (hK : K ⊆ closedBall (0 : E) M) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    paddedNeighborhood K a b ⊆ closedBall (0 : E) (a * M + b) := by
  rintro x ⟨y, ⟨k, hk, rfl⟩, z, ⟨w, hw, rfl⟩, rfl⟩
  rw [mem_closedBall_zero_iff]
  calc
    ‖a • k + b • w‖ ≤ ‖a • k‖ + ‖b • w‖ := norm_add_le _ _
    _ = a * ‖k‖ + b * ‖w‖ := by
      simp [norm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * M + b * 1 := add_le_add
      (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp (hK hk)) ha)
      (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hw) hb)
    _ = a * M + b := by ring

lemma paddedNeighborhood_absConvex {K : Set E} (hK : AbsConvex 𝕜 K)
    (a b : ℝ) : AbsConvex 𝕜 (paddedNeighborhood K a b) :=
  ⟨(hK.1.smul a).add (balanced_closedBall_zero.smul b),
    (hK.2.smul a).add ((convex_closedBall (0 : E) 1).smul b)⟩

lemma paddedNeighborhood_mem_nhds {K : Set E} (h0 : (0 : E) ∈ K)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    paddedNeighborhood K a b ∈ 𝓝 (0 : E) :=
  mem_of_superset (closedBall_mem_nhds _ hb)
    (closedBall_subset_paddedNeighborhood h0 a hb)

lemma paddedNeighborhood_absorbent {K : Set E} (h0 : (0 : E) ∈ K)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Absorbent ℝ (paddedNeighborhood K a b) :=
  absorbent_nhds_zero (paddedNeighborhood_mem_nhds h0 a hb)

lemma dfjpNeighborhood_absConvex {K : Set E} (hK : AbsConvex 𝕜 K) (j : ℤ) :
    AbsConvex 𝕜 (dfjpNeighborhood K j) :=
  paddedNeighborhood_absConvex hK _ _

lemma dfjpNeighborhood_mem_nhds {K : Set E} (h0 : (0 : E) ∈ K) (j : ℤ) :
    dfjpNeighborhood K j ∈ 𝓝 (0 : E) :=
  paddedNeighborhood_mem_nhds h0 _ (zpow_pos two_pos _)

lemma dfjpNeighborhood_absorbent {K : Set E} (h0 : (0 : E) ∈ K) (j : ℤ) :
    Absorbent ℝ (dfjpNeighborhood K j) :=
  absorbent_nhds_zero (dfjpNeighborhood_mem_nhds h0 j)

/-- The paper's gauge really is a seminorm over the original scalar field,
including the complex case. -/
def dfjpGaugeSeminorm {K : Set E} (hK : AbsConvex 𝕜 K) (h0 : (0 : E) ∈ K)
    (j : ℤ) : Seminorm 𝕜 E :=
  gaugeSeminorm (dfjpNeighborhood_absConvex hK j).1
    (dfjpNeighborhood_absConvex hK j).2 (dfjpNeighborhood_absorbent h0 j)

@[simp] lemma dfjpGaugeSeminorm_apply {K : Set E} (hK : AbsConvex 𝕜 K)
    (h0 : (0 : E) ∈ K) (j : ℤ) (x : E) :
    dfjpGaugeSeminorm hK h0 j x = dfjpGauge K j x := rfl

lemma dfjpGauge_nonneg (K : Set E) (j : ℤ) (x : E) : 0 ≤ dfjpGauge K j x :=
  gauge_nonneg _

lemma dfjpGauge_le_norm {K : Set E} (h0 : (0 : E) ∈ K) (j : ℤ) (x : E) :
    dfjpGauge K j x ≤ ‖x‖ / (2 : ℝ) ^ (-j) := by
  have hb : 0 < (2 : ℝ) ^ (-j) := zpow_pos two_pos _
  have h := mul_gauge_le_norm
    (ball_subset_closedBall.trans (closedBall_subset_paddedNeighborhood h0 ((2 : ℝ) ^ j) hb)) (x := x)
  exact (le_div_iff₀ hb).2 (by simpa [mul_comm, dfjpGauge, dfjpNeighborhood] using h)

lemma norm_div_le_dfjpGauge {K : Set E} (h0 : (0 : E) ∈ K) {M : ℝ}
    (hM : 0 ≤ M) (hK : K ⊆ closedBall (0 : E) M) (j : ℤ) (x : E) :
    ‖x‖ / ((2 : ℝ) ^ j * M + (2 : ℝ) ^ (-j)) ≤ dfjpGauge K j x := by
  apply le_gauge_of_subset_closedBall (dfjpNeighborhood_absorbent h0 j)
  · positivity
  · exact paddedNeighborhood_subset_closedBall hK (le_of_lt (zpow_pos two_pos _))
      (le_of_lt (zpow_pos two_pos _))

lemma dfjpGauge_eq_zero_iff {K : Set E} (h0 : (0 : E) ∈ K) {M : ℝ}
    (hM : 0 ≤ M) (hK : K ⊆ closedBall (0 : E) M) (j : ℤ) (x : E) :
    dfjpGauge K j x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h := norm_div_le_dfjpGauge h0 hM hK j x
    have hr : 0 < (2 : ℝ) ^ j * M + (2 : ℝ) ^ (-j) := by positivity
    rw [hx, div_le_iff₀ hr, zero_mul] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg x))
  · rintro rfl
    exact gauge_zero

lemma continuous_dfjpGauge {K : Set E} (hK : AbsConvex 𝕜 K)
    (h0 : (0 : E) ∈ K) (j : ℤ) : Continuous (dfjpGauge K j) :=
  continuous_gauge (dfjpNeighborhood_absConvex hK j).2
    (dfjpNeighborhood_mem_nhds h0 j)

end SurveyStatements.P4
