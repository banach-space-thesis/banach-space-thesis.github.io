import BanachIsometric.RadialHomeomorphism
import BanachIsometric.LipschitzCone

/-! The actual radial gauge homeomorphism and its actual inverse are globally
Lipschitz when the definite homogeneous gauge is Lipschitz on the sphere.
This regularity needs neither convexity nor a triangle inequality for the
gauge, and retains the original norm. -/

noncomputable section
namespace BanachIsometric
open Set Metric NormedSpace
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem lipschitzWith_sphere_scalar_smul {a : sphere (0 : V) 1 → ℝ} {L M : ℝ≥0}
    (ha : LipschitzWith L a) (hM : ∀ u, |a u| ≤ M) :
    LipschitzWith (M + L) (fun u => a u • u.val) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hu : ‖u.val‖ = 1 := norm_eq_of_mem_sphere u
  have hv : ‖v.val‖ = 1 := norm_eq_of_mem_sphere v
  have hd : |a u - a v| ≤ (L : ℝ) * dist u v := by
    simpa only [Real.dist_eq] using ha.dist_le_mul u v
  rw [dist_eq_norm]
  have he : a u • u.val - a v • v.val =
      a u • (u.val - v.val) + (a u - a v) • v.val := by
    rw [smul_sub, sub_smul]
    abel
  calc
    _ ≤ ‖a u • (u.val - v.val)‖ + ‖(a u - a v) • v.val‖ := by
      rw [he]
      exact norm_add_le _ _
    _ = |a u| * dist u v + |a u - a v| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hv, mul_one]
      rw [Subtype.dist_eq, dist_eq_norm]
    _ ≤ (M : ℝ) * dist u v + (L : ℝ) * dist u v :=
      add_le_add (mul_le_mul_of_nonneg_right (hM u) dist_nonneg) hd
    _ = ((M + L : ℝ≥0) : ℝ) * dist u v := by push_cast; ring

theorem radialGaugeMapInv_eq_cone {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) :
    radialGaugeMapInv p = coneExtension (fun u : sphere (0 : V) 1 => p u.val • u.val) := by
  funext x
  by_cases hx : x = 0
  · simp [hx]
  rw [coneExtension_of_ne _ x hx]
  change (p x / ‖x‖) • x = ‖x‖ • (p (‖x‖⁻¹ • x) • (‖x‖⁻¹ • x))
  rw [hp.smul_nonneg _ (inv_nonneg.mpr (norm_nonneg x)), smul_smul, smul_smul]
  congr 1
  field_simp

theorem radialGaugeMap_eq_cone {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) :
    radialGaugeMap p = coneExtension (fun u : sphere (0 : V) 1 => (p u.val)⁻¹ • u.val) := by
  funext x
  by_cases hx : x = 0
  · simp [hx]
  rw [coneExtension_of_ne _ x hx]
  change (‖x‖ / p x) • x = ‖x‖ • ((p (‖x‖⁻¹ • x))⁻¹ • (‖x‖⁻¹ • x))
  rw [hp.smul_nonneg _ (inv_nonneg.mpr (norm_nonneg x)), smul_smul, smul_smul]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hx, (hp.pos hx).ne']

theorem exists_lipschitz_radialGaugeMapInv [FiniteDimensional ℝ V]
    {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) {L : ℝ≥0}
    (hL : LipschitzOnWith L p (sphere (0 : V) 1)) :
    ∃ C : ℝ≥0, LipschitzWith C (radialGaugeMapInv p) := by
  obtain ⟨C, hC⟩ := hp.exists_lipschitzWith hL
  have hSphere : LipschitzWith C (fun u : sphere (0 : V) 1 => p u.val) := by
    simpa only [mul_one] using hC.comp (LipschitzWith.subtype_val _)
  have hBound : ∀ u : sphere (0 : V) 1, |p u.val| ≤ C := by
    intro u
    have h := hC.dist_le_mul u.val 0
    simpa only [(hp.eq_zero_iff 0).mpr rfl, dist_zero_right, Real.norm_eq_abs,
      norm_eq_of_mem_sphere u, mul_one] using h
  obtain ⟨D, hD⟩ := exists_lipschitz_coneExtension (lipschitzWith_sphere_scalar_smul hSphere hBound)
  exact ⟨D, by rwa [radialGaugeMapInv_eq_cone hp]⟩

theorem exists_lipschitz_radialGaugeMap [FiniteDimensional ℝ V]
    {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) {L : ℝ≥0}
    (hL : LipschitzOnWith L p (sphere (0 : V) 1)) :
    ∃ C : ℝ≥0, LipschitzWith C (radialGaugeMap p) := by
  obtain ⟨C, hC⟩ := hp.exists_lipschitzWith hL
  obtain ⟨ε, _, hε, _, hcomp⟩ := hp.exists_norm_comparison hC.continuous.continuousOn
  let εn : ℝ≥0 := ⟨ε, hε.le⟩
  have hLower : ∀ u : sphere (0 : V) 1, ε ≤ p u.val := by
    intro u
    simpa only [norm_eq_of_mem_sphere u, mul_one] using (hcomp u.val).1
  have hPos : ∀ u : sphere (0 : V) 1, 0 < p u.val := fun u => hε.trans_le (hLower u)
  have hInvLip : LipschitzWith (C / (εn * εn)) (fun u : sphere (0 : V) 1 => (p u.val)⁻¹) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_inv_inv₀ (hPos u).ne' (hPos v).ne']
    have hden : ε * ε ≤ ‖p u.val‖ * ‖p v.val‖ := by
      rw [Real.norm_of_nonneg (hPos u).le, Real.norm_of_nonneg (hPos v).le]
      exact mul_le_mul (hLower u) (hLower v) hε.le (hPos u).le
    calc
      _ ≤ dist (p u.val) (p v.val) / (ε * ε) :=
        div_le_div_of_nonneg_left dist_nonneg (mul_pos hε hε) hden
      _ ≤ ((C : ℝ) * dist u v) / (ε * ε) :=
        div_le_div_of_nonneg_right (hC.dist_le_mul u.val v.val) (mul_nonneg hε.le hε.le)
      _ = ((C / (εn * εn) : ℝ≥0) : ℝ) * dist u v := by
        change ((C : ℝ) * dist u v) / (ε * ε) = ((C : ℝ) / (ε * ε)) * dist u v
        ring
  have hInvBound : ∀ u : sphere (0 : V) 1, |(p u.val)⁻¹| ≤ (εn⁻¹ : ℝ≥0) := by
    intro u
    rw [abs_of_pos (inv_pos.mpr (hPos u))]
    exact (inv_le_inv₀ (hPos u) hε).mpr (hLower u)
  obtain ⟨D, hD⟩ := exists_lipschitz_coneExtension (lipschitzWith_sphere_scalar_smul hInvLip hInvBound)
  exact ⟨D, by rwa [radialGaugeMap_eq_cone hp]⟩

end BanachIsometric
