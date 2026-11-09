import BanachIsometric.PiolaBoxFrontier

/-! # An actual coordinate cube enclosing the Euclidean unit ball -/

namespace BanachIsometric

open Set Metric Filter
open scoped Topology

def coordinateCubeLower (n : ℕ) (R : ℝ) : PiolaSpace n := fun _ => -R
def coordinateCubeUpper (n : ℕ) (R : ℝ) : PiolaSpace n := fun _ => R

theorem coordinateCube_lower_le_upper (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    coordinateCubeLower n R ≤ coordinateCubeUpper n R := by
  intro i
  change -R ≤ R
  linarith

theorem mem_coordinateCube_of_norm_le {n : ℕ} {R : ℝ} {x : PiolaSpace n} (hx : ‖x‖ ≤ R) :
    x ∈ Icc (coordinateCubeLower n R) (coordinateCubeUpper n R) := by
  have hcoord (i : Fin n) : |x i| ≤ R := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (f := x) i).trans hx
  exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩

theorem zero_mem_interior_coordinateCube (n : ℕ) {R : ℝ} (hR : 0 < R) :
    (0 : PiolaSpace n) ∈ interior (Icc (coordinateCubeLower n R) (coordinateCubeUpper n R)) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ball_mem_nhds (0 : PiolaSpace n) hR)
  intro x hx
  apply mem_coordinateCube_of_norm_le
  exact (by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < R).le

theorem coordinate_image_unitBall_mem_cube
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (e : V ≃L[ℝ] PiolaSpace n) {R : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ ≤ R)
    {x : V} (hx : x ∈ closedBall (0 : V) 1) :
    e x ∈ Icc (coordinateCubeLower n R) (coordinateCubeUpper n R) := by
  apply mem_coordinateCube_of_norm_le
  have hx' : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
  exact ((e : V →L[ℝ] PiolaSpace n).le_opNorm x).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hx').trans hR)

theorem coordinateCube_boundary_preimage_norm_gt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (e : V ≃L[ℝ] PiolaSpace n) {R : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R)
    {x : PiolaSpace n} (hx : x ∈ piolaBoxBoundary (coordinateCubeLower n R) (coordinateCubeUpper n R)) :
    1 < ‖e.symm x‖ := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  obtain ⟨_hxbox, i, hi⟩ := mem_piolaBoxBoundary_iff.mp hx
  have hcoord : ‖x i‖ = R := by
    rcases hi with hi | hi
    · rw [hi]
      change ‖(-R : ℝ)‖ = R
      rw [norm_neg, Real.norm_of_nonneg hRpos.le]
    · rw [hi]
      exact Real.norm_of_nonneg hRpos.le
  have hnorm : R ≤ ‖x‖ := by simpa only [hcoord] using norm_le_pi_norm (f := x) i
  have hop := (e : V →L[ℝ] PiolaSpace n).le_opNorm (e.symm x)
  change ‖e (e.symm x)‖ ≤ ‖(e : V →L[ℝ] PiolaSpace n)‖ * ‖e.symm x‖ at hop
  rw [e.apply_symm_apply] at hop
  by_contra hnot
  have hle : ‖e.symm x‖ ≤ 1 := le_of_not_gt hnot
  have hupper := mul_le_of_le_one_right (norm_nonneg (e : V →L[ℝ] PiolaSpace n)) hle
  linarith

end BanachIsometric
