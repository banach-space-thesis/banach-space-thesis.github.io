import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.Basic

/-! Actual centered balls of the original compatible metric and their
Minkowski functionals. No norm metric is substituted for the given metric. -/

namespace BanachIsometric.MetricGeometry

open Set Filter
open scoped Topology Pointwise

noncomputable section

def TranslationInvariant {X : Type*} [AddCommGroup X] [MetricSpace X] : Prop :=
  ∀ x y z : X, dist (x + z) (y + z) = dist x y

theorem dist_eq_dist_sub_zero {X : Type*} [AddCommGroup X] [MetricSpace X]
    (h : TranslationInvariant (X := X)) (x y : X) : dist x y = dist (x - y) 0 := by
  have he := h x y (-y)
  simpa only [sub_eq_add_neg, add_neg_cancel] using he.symm

section AlgebraicGauge

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem gauge_image_linearEquiv (e : E ≃ₗ[ℝ] F) (s : Set E) (x : E) :
    gauge (e '' s) (e x) = gauge s x := by
  rw [gauge_def', gauge_def']
  congr 1
  ext r
  apply and_congr_right
  intro _
  rw [← e.map_smul]
  constructor
  · rintro ⟨y, hy, he⟩
    rwa [e.injective he] at hy
  · intro hx
    exact ⟨_, hx, rfl⟩

theorem gauge_preimage_submodule (s : Set E) (P : Submodule ℝ E) (x : P) :
    gauge (P.subtype ⁻¹' s) x = gauge s x.val := by
  rw [gauge_def', gauge_def']
  rfl

end AlgebraicGauge

section MetricEquivalence

variable {R E F : Type*} [Semiring R] [AddCommGroup E] [Module R E] [MetricSpace E]
    [AddCommGroup F] [Module R F] [MetricSpace F]

theorem linearMetricEquiv_image_centeredBall (e : E ≃ₗ[R] F) (he : Isometry e) (r : ℝ) :
    e '' Metric.closedBall (0 : E) r = Metric.closedBall (0 : F) r := by
  have hd (x : E) : dist (e x) 0 = dist x 0 := by
    rw [← e.map_zero]
    exact he.dist_eq x 0
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change dist (e x) 0 ≤ r
    rw [hd]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change dist (e.symm y) 0 ≤ r
    rw [← hd, e.apply_symm_apply]
    exact hy

end MetricEquivalence

section CenteredGauge

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]

def centeredBallGauge (r : ℝ) : X → ℝ := gauge (Metric.closedBall (0 : X) r)

theorem centeredBallGauge_submodule (P : Submodule ℝ X) (r : ℝ) (x : P) :
    centeredBallGauge (X := P) r x = centeredBallGauge (X := X) r x.val :=
  gauge_preimage_submodule (Metric.closedBall (0 : X) r) P x

theorem centeredBallGauge_preserved {Y : Type*} [AddCommGroup Y] [Module ℝ Y] [MetricSpace Y]
    (e : X ≃ₗ[ℝ] Y) (he : Isometry e) (r : ℝ) (x : X) :
    centeredBallGauge r (e x) = centeredBallGauge r x := by
  have h := gauge_image_linearEquiv e (Metric.closedBall (0 : X) r) x
  rw [linearMetricEquiv_image_centeredBall e he r] at h
  exact h

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

omit [Module ℝ X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] in
theorem centeredBall_mem_nhds {r : ℝ} (hr : 0 < r) : Metric.closedBall (0 : X) r ∈ 𝓝 (0 : X) :=
  mem_of_superset (Metric.ball_mem_nhds (0 : X) hr) Metric.ball_subset_closedBall

omit [IsTopologicalAddGroup X] in
theorem centeredBall_absorbent {r : ℝ} (hr : 0 < r) : Absorbent ℝ (Metric.closedBall (0 : X) r) :=
  absorbent_nhds_zero (centeredBall_mem_nhds hr)

def centeredBallSeminorm (r : ℝ) (hr : 0 < r) (hb : Balanced ℝ (Metric.closedBall (0 : X) r))
    (hc : Convex ℝ (Metric.closedBall (0 : X) r)) : Seminorm ℝ X :=
  gaugeSeminorm hb hc (centeredBall_absorbent hr)

theorem continuous_centeredBallGauge {r : ℝ} (hr : 0 < r)
    (hc : Convex ℝ (Metric.closedBall (0 : X) r)) : Continuous (centeredBallGauge (X := X) r) :=
  continuous_gauge hc (centeredBall_mem_nhds hr)

theorem centeredBallGauge_le_one_iff {r : ℝ} (hr : 0 < r)
    (hc : Convex ℝ (Metric.closedBall (0 : X) r)) (x : X) :
    centeredBallGauge r x ≤ 1 ↔ dist x 0 ≤ r := by
  have h := gauge_le_one_iff_mem_closure hc (centeredBall_mem_nhds hr) (x := x)
  simpa only [Metric.isClosed_closedBall.closure_eq, Metric.mem_closedBall] using h

theorem centeredBallGauge_nonzero_of_proper {r : ℝ} (hr : 0 < r)
    (hc : Convex ℝ (Metric.closedBall (0 : X) r)) (hproper : Metric.closedBall (0 : X) r ≠ univ) :
    ∃ x : X, centeredBallGauge r x ≠ 0 := by
  by_contra hn
  apply hproper
  apply eq_univ_of_forall
  intro x
  apply (centeredBallGauge_le_one_iff hr hc x).mp
  have hx : centeredBallGauge r x = 0 := not_not.mp (not_exists.mp hn x)
  rw [hx]
  exact zero_le_one

end CenteredGauge

end
end BanachIsometric.MetricGeometry
