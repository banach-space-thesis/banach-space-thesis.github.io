import BanachIsometric.SphereSignedDegree

/-!
# Close Lipschitz sphere maps have the same actual signed degree

The ordinary affine interpolation is a nonvanishing ambient-valued homotopy.
The nonvanishing cone theorem applies directly, so no unproved normalization
or sphere-homotopy regularity property is needed.
-/

namespace BanachIsometric

open Set Metric
open scoped Topology NNReal

theorem sphereSignedDegree_eq_of_close
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {f g : sphere (0 : V) 1 → sphere (0 : V) 1} {Cf Cg : ℝ≥0}
    (hf : LipschitzWith Cf f) (hg : LipschitzWith Cg g)
    (hclose : ∀ z, dist (f z) (g z) < 1) : sphereSignedDegree e f = sphereSignedDegree e g := by
  let H : unitInterval → sphere (0 : V) 1 → V := fun t z => realAffine t (f z).val (g z).val
  have hH : Continuous (fun z : unitInterval × sphere (0 : V) 1 => H z.1 z.2) := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (hf.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (hg.continuous.comp continuous_snd)))
  have hLip : ∀ t, ∃ L : ℝ≥0, LipschitzWith L (H t) := by
    intro t
    refine ⟨Cf + Cg, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    calc
      dist (H t x) (H t y) ≤ dist (f x).val (f y).val + dist (g x).val (g y).val :=
        dist_realAffine_le_add t _ _ _ _
      _ ≤ (Cf : ℝ) * dist x y + (Cg : ℝ) * dist x y :=
        add_le_add (by simpa only [Subtype.dist_eq] using hf.dist_le_mul x y)
          (by simpa only [Subtype.dist_eq] using hg.dist_le_mul x y)
      _ = ((Cf + Cg : ℝ≥0) : ℝ) * dist x y := by push_cast; ring
  have hne : ∀ t z, H t z ≠ 0 := by
    intro t z hz
    have hdist := dist_realAffine_le_add t (f z).val (g z).val (f z).val (f z).val
    rw [realAffine_self, dist_self, zero_add] at hdist
    change dist (H t z) (f z).val ≤ dist (g z).val (f z).val at hdist
    have hnorm : ‖(f z).val‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using (f z).property
    rw [hz, dist_zero_left, hnorm] at hdist
    have hclose' : dist (g z).val (f z).val < 1 := by
      simpa only [Subtype.dist_eq, dist_comm] using hclose z
    linarith
  let R : ℝ := ‖(e : V →L[ℝ] PiolaSpace n)‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hindex := localSignedIndex_coordinate_nonvanishing_cone_homotopy_of_zero_mem_interior
    e H hH hLip hne (coordinateCubeLower n R) (coordinateCubeUpper n R)
    (coordinateCube_lower_le_upper n hR.le) (zero_mem_interior_coordinateCube n hR)
    (0 : unitInterval) 1
  have h0 : H 0 = (fun z => (f z).val) := by
    funext z
    change (1 - (0 : ℝ)) • (f z).val + (0 : ℝ) • (g z).val = (f z).val
    simp
  have h1 : H 1 = (fun z => (g z).val) := by
    funext z
    change (1 - (1 : ℝ)) • (f z).val + (1 : ℝ) • (g z).val = (g z).val
    simp
  rw [h0, h1] at hindex
  exact hindex

end BanachIsometric
