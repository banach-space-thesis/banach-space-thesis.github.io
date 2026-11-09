import BanachIsometric.RadialStarBody
import BanachIsometric.SphereHomotopy

/-!
# The actual radial homeomorphism used in the cone-degree argument

For a continuous definite positively homogeneous gauge `p`, the radial map
`x ↦ (‖x‖ / p x) • x` maps the Euclidean unit ball onto the gauge body. Its
inverse and continuity at zero are proved explicitly, without convexity,
symmetry, or any assumed degree formula.
-/

namespace BanachIsometric

open Set NormedSpace
open scoped Topology Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def radialGaugeMap (p : V → ℝ) (x : V) : V := (‖x‖ / p x) • x

noncomputable def radialGaugeMapInv (p : V → ℝ) (x : V) : V := (p x / ‖x‖) • x

@[simp] theorem radialGaugeMap_zero (p : V → ℝ) : radialGaugeMap p 0 = 0 := by
  simp [radialGaugeMap]

@[simp] theorem radialGaugeMapInv_zero (p : V → ℝ) : radialGaugeMapInv p 0 = 0 := by
  simp [radialGaugeMapInv]

theorem gauge_radialGaugeMap {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) (x : V) :
    p (radialGaugeMap p x) = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, (hp.eq_zero_iff 0).mpr rfl]
  rw [radialGaugeMap, hp.smul_nonneg _ (div_nonneg (norm_nonneg _) (hp.nonneg _)),
    div_mul_cancel₀ _ (hp.pos hx).ne']

theorem norm_radialGaugeMapInv {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) (x : V) :
    ‖radialGaugeMapInv p x‖ = p x := by
  by_cases hx : x = 0
  · simp [hx, (hp.eq_zero_iff 0).mpr rfl]
  rw [radialGaugeMapInv, norm_smul,
    Real.norm_of_nonneg (div_nonneg (hp.nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem radialGaugeMapInv_map {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) (x : V) :
    radialGaugeMapInv p (radialGaugeMap p x) = x := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hpz : p x ≠ 0 := (hp.pos hx).ne'
  rw [radialGaugeMapInv, gauge_radialGaugeMap hp, radialGaugeMap, norm_smul,
    Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (hp.nonneg _)), smul_smul]
  have hc : ‖x‖ / (‖x‖ / p x * ‖x‖) * (‖x‖ / p x) = 1 := by field_simp [hn, hpz]
  rw [hc, one_smul]

theorem radialGaugeMap_mapInv {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) (x : V) :
    radialGaugeMap p (radialGaugeMapInv p x) = x := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hpz : p x ≠ 0 := (hp.pos hx).ne'
  rw [radialGaugeMap, norm_radialGaugeMapInv hp, radialGaugeMapInv,
    hp.smul_nonneg _ (div_nonneg (hp.nonneg _) (norm_nonneg _)), smul_smul]
  have hc : p x / (p x / ‖x‖ * p x) * (p x / ‖x‖) = 1 := by field_simp [hn, hpz]
  rw [hc, one_smul]

theorem radialGaugeMap_norm_le {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    {ε : ℝ} (hε : 0 < ε) (hlower : ∀ x, ε * ‖x‖ ≤ p x) (x : V) :
    ‖radialGaugeMap p x‖ ≤ ε⁻¹ * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hpx : 0 < p x := hp.pos hx
  rw [radialGaugeMap, norm_smul,
    Real.norm_of_nonneg (div_nonneg hn.le hpx.le)]
  apply mul_le_mul_of_nonneg_right ?_ hn.le
  apply (div_le_iff₀ hpx).mpr
  calc
    ‖x‖ = ε⁻¹ * (ε * ‖x‖) := by rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    _ ≤ ε⁻¹ * p x := mul_le_mul_of_nonneg_left (hlower x) (inv_nonneg.mpr hε.le)

theorem continuous_radialGaugeMapInv {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    (hcont : Continuous p) : Continuous (radialGaugeMapInv p) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    change Filter.Tendsto (radialGaugeMapInv p) (𝓝 0) (𝓝 (radialGaugeMapInv p 0))
    rw [radialGaugeMapInv_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_radialGaugeMapInv hp, (hp.eq_zero_iff 0).mpr rfl] using
      hcont.continuousAt.tendsto (x := (0 : V))
  · exact (hcont.continuousAt.div continuousAt_id.norm (norm_ne_zero_iff.mpr hx)).smul
      continuousAt_id

theorem continuous_radialGaugeMap {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    (hcont : Continuous p) {ε : ℝ} (hε : 0 < ε) (hlower : ∀ x, ε * ‖x‖ ≤ p x) :
    Continuous (radialGaugeMap p) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro δ hδ
    refine ⟨δ * ε, mul_pos hδ hε, ?_⟩
    intro y hy
    rw [radialGaugeMap_zero, dist_zero_right]
    have hy' : ‖y‖ < δ * ε := by simpa only [dist_zero_right] using hy
    calc
      ‖radialGaugeMap p y‖ ≤ ε⁻¹ * ‖y‖ := radialGaugeMap_norm_le hp hε hlower y
      _ < ε⁻¹ * (δ * ε) := mul_lt_mul_of_pos_left hy' (inv_pos.mpr hε)
      _ = δ := by field_simp
  · exact (continuousAt_id.norm.div hcont.continuousAt ((hp.eq_zero_iff x).not.mpr hx)).smul
      continuousAt_id

/-- The radial homeomorphism in the cone argument, constructed from the
actual gauge and retaining its exact radial values. -/
noncomputable def radialGaugeHomeomorph {p : V → ℝ} [FiniteDimensional ℝ V]
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) : V ≃ₜ V where
  toFun := radialGaugeMap p
  invFun := radialGaugeMapInv p
  left_inv := radialGaugeMapInv_map hp
  right_inv := radialGaugeMap_mapInv hp
  continuous_toFun := by
    obtain ⟨ε, _, hε, _, hbound⟩ := hp.exists_norm_comparison hcont.continuousOn
    exact continuous_radialGaugeMap hp hcont hε (fun x => (hbound x).1)
  continuous_invFun := continuous_radialGaugeMapInv hp hcont

theorem radialGaugeHomeomorph_image_ball {p : V → ℝ} [FiniteDimensional ℝ V]
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) (r : ℝ) :
    radialGaugeHomeomorph hp hcont '' Metric.ball (0 : V) r = {x | p x < r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change p (radialGaugeMap p x) < r
    rw [gauge_radialGaugeMap hp]
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  · intro hy
    refine ⟨radialGaugeMapInv p y, ?_, radialGaugeMap_mapInv hp y⟩
    simpa only [Metric.mem_ball, dist_zero_right, norm_radialGaugeMapInv hp] using hy

end BanachIsometric
