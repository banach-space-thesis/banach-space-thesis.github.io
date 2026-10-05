import ThesisCommon.Analysis.GowersMaureyRationalApproximation

/-! Rational approximation with room inside the actual dual unit ball.
The rational object is the divided block, so its subsequent average has
Gaussian-rational coordinates even when the averaging weight is irrational. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem mass_real_smul (r : ℝ) (a : C00 𝕜) : mass (r • a) = |r| * mass a := by
  simpa only [Real.norm_eq_abs] using map_smul_eq_mul ((mass (𝕜 := 𝕜)).restrictScalars ℝ) r a

theorem exists_rational_divided_dualUnit_near (D : ConstructionData 𝕜)
    {z : C00 𝕜} (hz : DualUnit (implicitNorm D) z)
    {q f ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hf : 0 < f) (hε : 0 < ε) :
    ∃ g : C00 𝕜, (∀ n, RationalCoordinate (g n)) ∧ g.support ⊆ z.support ∧
      mass (g - (q/f) • z) < ε ∧ DualUnit (implicitNorm D) (f • g) := by
  have hmargin : 0 < (1-q)/f := div_pos (sub_pos.mpr hq1) hf
  obtain ⟨g,hg,hgs,herr⟩ := exists_rational_finsupp_near ((q/f) • z)
    (lt_min hε hmargin)
  refine ⟨g,hg,hgs.trans Finsupp.support_smul,
    herr.trans_le (min_le_left _ _),?_⟩
  have hbound : q + f * mass (g-(q/f) • z) ≤ 1 := by
    have h := (le_div_iff₀ hf).mp ((herr.trans_le (min_le_right _ _)).le)
    nlinarith
  have he : f • g = q • z + f • (g-(q/f) • z) := by
    rw [smul_sub, smul_smul]
    have hmul : f * (q/f) = q := by field_simp
    rw [hmul]
    abel
  intro x
  rw [he, pairing_add_left]
  calc
    _ ≤ ‖pairing (q • z) x‖ + ‖pairing (f • (g-(q/f) • z)) x‖ := norm_add_le _ _
    _ = q * ‖pairing z x‖ + f * ‖pairing (g-(q/f) • z) x‖ := by
      rw [pairing_real_smul_left, pairing_real_smul_left, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq0, abs_of_pos hf]
    _ ≤ q * implicitNorm D x + f * (mass (g-(q/f) • z) * implicitNorm D x) :=
      add_le_add (mul_le_mul_of_nonneg_left (hz x) hq0)
        (mul_le_mul_of_nonneg_left (pairing_norm_le_mass_mul_implicitNorm D _ _) hf.le)
    _ = (q + f * mass (g-(q/f) • z)) * implicitNorm D x := by ring
    _ ≤ implicitNorm D x := mul_le_of_le_one_left (apply_nonneg _ _) hbound

end ThesisCommon.GowersMaurey
