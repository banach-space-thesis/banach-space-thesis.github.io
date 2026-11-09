import BanachIsometric.RadialHomeomorphism

/-!
# Positive radial interpolation

The radial map used in the cone argument is homotopic to the identity by an
explicit interpolation which never sends a nonzero vector to zero. This is
the geometric input for its orientation sign; no degree equality is assumed.
-/

namespace BanachIsometric

open Set NormedSpace
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def radialGaugeInterpolation (p : V → ℝ) (t : unitInterval) (x : V) : V :=
  (1 - (t : ℝ)) • x + (t : ℝ) • radialGaugeMap p x

@[simp] theorem radialGaugeInterpolation_zero (p : V → ℝ) (x : V) :
    radialGaugeInterpolation p 0 x = x := by simp [radialGaugeInterpolation]

@[simp] theorem radialGaugeInterpolation_one (p : V → ℝ) (x : V) :
    radialGaugeInterpolation p 1 x = radialGaugeMap p x := by simp [radialGaugeInterpolation]

theorem radialGaugeInterpolation_ne_zero {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (t : unitInterval) {x : V} (hx : x ≠ 0) :
    radialGaugeInterpolation p t x ≠ 0 := by
  have ha : 0 < ‖x‖ / p x := div_pos (norm_pos_iff.mpr hx) (hp.pos hx)
  have hc : 0 < (1 - (t : ℝ)) + (t : ℝ) * (‖x‖ / p x) := by
    by_cases ht : (t : ℝ) = 0
    · simp [ht]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2)
        (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) ha)
  rw [radialGaugeInterpolation, radialGaugeMap, smul_smul, ← add_smul]
  exact smul_ne_zero hc.ne' hx

theorem continuous_radialGaugeInterpolation {p : V → ℝ}
    (hmap : Continuous (radialGaugeMap p)) :
    Continuous (fun z : unitInterval × V => radialGaugeInterpolation p z.1 z.2) := by
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).smul (hmap.comp continuous_snd))

noncomputable def radialGaugeHomotopy {p : V → ℝ} [FiniteDimensional ℝ V]
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) :
    ContinuousMap.Homotopy (ContinuousMap.id V)
      ⟨radialGaugeMap p, (radialGaugeHomeomorph hp hcont).continuous⟩ where
  toFun z := radialGaugeInterpolation p z.1 z.2
  continuous_toFun := continuous_radialGaugeInterpolation (radialGaugeHomeomorph hp hcont).continuous
  map_zero_left := radialGaugeInterpolation_zero p
  map_one_left := radialGaugeInterpolation_one p

theorem normalize_radialGaugeMap {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    {x : V} (hx : x ≠ 0) : normalize (radialGaugeMap p x) = normalize x := by
  exact normalize_smul_of_pos (div_pos (norm_pos_iff.mpr hx) (hp.pos hx)) x

theorem radialGaugeHomeomorph_image_closedBall {p : V → ℝ} [FiniteDimensional ℝ V]
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) (r : ℝ) :
    radialGaugeHomeomorph hp hcont '' Metric.closedBall (0 : V) r = {x | p x ≤ r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change p (radialGaugeMap p x) ≤ r
    rw [gauge_radialGaugeMap hp]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  · intro hy
    refine ⟨radialGaugeMapInv p y, ?_, radialGaugeMap_mapInv hp y⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_radialGaugeMapInv hp] using hy

theorem radialGaugeHomeomorph_image_sphere {p : V → ℝ} [FiniteDimensional ℝ V]
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) (r : ℝ) :
    radialGaugeHomeomorph hp hcont '' Metric.sphere (0 : V) r = {x | p x = r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change p (radialGaugeMap p x) = r
    rw [gauge_radialGaugeMap hp]
    simpa only [Metric.mem_sphere, dist_zero_right] using hx
  · intro hy
    refine ⟨radialGaugeMapInv p y, ?_, radialGaugeMap_mapInv hp y⟩
    simpa only [Metric.mem_sphere, dist_zero_right, norm_radialGaugeMapInv hp] using hy

end BanachIsometric
