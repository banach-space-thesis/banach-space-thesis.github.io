import ThesisCommon.Analysis.SequenceCoordinates
import Mathlib.Analysis.Normed.Operator.Compact

/-! Coordinate decay on compact subsets of actual finite-p sequence spaces.
This is the compactness input in LPCK's forward reduction. -/
noncomputable section
open scoped ENNReal Topology
open Filter
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_norm_coordinates_tendsto_zero (hp : p ≠ ∞) (x : lp (fun _ : ℕ => Y) p) :
    Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  have ht := ((lp.memℓp x).summable hp').tendsto_atTop_zero
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (norm_nonneg _))
  · intro ε hε
    filter_upwards [ht.eventually_lt_const (Real.rpow_pos_of_pos hε p.toReal)] with n hn
    by_contra h
    have hle := Real.rpow_le_rpow hε.le (le_of_not_gt h) hp'.le
    exact (not_lt_of_ge hle) hn

theorem IsCompact.lp_coordinates_uniformly_small (hp : p ≠ ∞)
    {K : Set (lp (fun _ : ℕ => Y) p)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ‖x n‖ < ε := by
  obtain ⟨s, _, hfin, hcover⟩ := hK.finite_cover_balls (half_pos hε)
  have hs : ∀ᶠ n in atTop, ∀ y ∈ s, ‖y n‖ < ε/2 :=
    (hfin.eventually_all).2 (fun y _ =>
      (lp_norm_coordinates_tendsto_zero hp y).eventually_lt_const (half_pos hε))
  filter_upwards [hs] with n hn
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (hcover hx)
  obtain ⟨hys, hxy⟩ := Set.mem_iUnion.1 hy
  have hdist : ‖x-y‖ < ε/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  calc
    ‖x n‖ ≤ ‖x n-y n‖ + ‖y n‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖x-y‖ + ‖y n‖ := add_le_add_right
      (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) (x-y) n) _
    _ < ε/2 + ε/2 := add_lt_add hdist (hn y hys)
    _ = ε := by ring

theorem IsCompactOperator.lp_coordinate_norm_tendsto_zero (hp : p ≠ ∞)
    {S : X →L[𝕜] lp (fun _ : ℕ => Y) p} (hS : IsCompactOperator S) :
    Tendsto (fun n => ‖(lpCoordinate p n).comp S‖) atTop (𝓝 0) := by
  obtain ⟨K, hK, hSK⟩ := hS.image_closedBall_subset_compact (f := S.toLinearMap) 1
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (norm_nonneg _))
  · intro ε hε
    filter_upwards [IsCompact.lp_coordinates_uniformly_small hp hK (half_pos hε)] with n hn
    apply lt_of_le_of_lt _ (half_lt_self hε)
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
    intro x hx
    exact (hn (S x) (hSK ⟨x, by simp [Metric.mem_closedBall, dist_zero_right, hx], rfl⟩)).le

end ThesisCommon
