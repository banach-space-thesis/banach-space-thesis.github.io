import PL1.Definitions

/-! # Elementary L1–L-infinity interpolation

The estimate follows pointwise from t^p ≤ M^(p-1) t. It applies to arbitrary
measures and every finite exponent p ≥ 1.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PL1.LpInterpolation

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω}

theorem eLpNorm_le_of_ae_bound (f : Ω → E) (hf : AEStronglyMeasurable f μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞) (M b : ℝ≥0∞)
    (hM : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M) (hb : eLpNorm f 1 μ ≤ b) :
    eLpNorm f p μ ≤ M ^ (1 - 1 / p.toReal) * b ^ (1 / p.toReal) := by
  have hpR : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hptop hp
  have hp0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpR
  have hpne : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpow : ∀ᵐ x ∂μ, ‖f x‖ₑ ^ p.toReal ≤ M ^ (p.toReal - 1) * ‖f x‖ₑ := by
    filter_upwards [hM] with x hx
    calc
      ‖f x‖ₑ ^ p.toReal = ‖f x‖ₑ ^ ((p.toReal - 1) + 1) := by rw [sub_add_cancel]
      _ = ‖f x‖ₑ ^ (p.toReal - 1) * ‖f x‖ₑ := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hpR) zero_le_one, ENNReal.rpow_one]
      _ ≤ M ^ (p.toReal - 1) * ‖f x‖ₑ :=
        mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hx (sub_nonneg.mpr hpR)) bot_le
  have hint : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≤ M ^ (p.toReal - 1) * b := by
    calc
      _ ≤ ∫⁻ x, M ^ (p.toReal - 1) * ‖f x‖ₑ ∂μ := lintegral_mono_ae hpow
      _ = M ^ (p.toReal - 1) * eLpNorm f 1 μ := by
        rw [lintegral_const_mul'' _ hf.enorm, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ M ^ (p.toReal - 1) * b := mul_le_mul_of_nonneg_left hb bot_le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hptop]
  calc
    _ ≤ (M ^ (p.toReal - 1) * b) ^ (1 / p.toReal) :=
      ENNReal.rpow_le_rpow hint (by positivity)
    _ = M ^ (1 - 1 / p.toReal) * b ^ (1 / p.toReal) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
      congr 2
      field_simp

theorem eLpNorm_le_of_ae_norm_bound (f : Lp E 1 μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞)
    (M : ℝ) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) :
    eLpNorm f p μ ≤ (ENNReal.ofReal M) ^ (1 - 1 / p.toReal) *
      (ENNReal.ofReal ‖f‖) ^ (1 / p.toReal) := by
  apply eLpNorm_le_of_ae_bound f (Lp.aestronglyMeasurable f) p hp hptop
  · filter_upwards [hM] with x hx
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx
  · simp only [ofReal_norm, Lp.enorm_def, le_refl]

private theorem interpolation_bound_ne_top (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞)
    (M b : ℝ) :
    (ENNReal.ofReal M) ^ (1 - 1 / p.toReal) *
      (ENNReal.ofReal b) ^ (1 / p.toReal) ≠ ∞ := by
  have hpR : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hptop hp
  have hp0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpR
  apply ENNReal.mul_ne_top
  · apply ENNReal.rpow_ne_top_of_nonneg _ ENNReal.ofReal_ne_top
    exact sub_nonneg.mpr ((div_le_one hp0).mpr hpR)
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

/-- Every bounded L1 function belongs to every finite Lp space with p ≥ 1. -/
theorem memLp_of_ae_norm_bound (f : Lp E 1 μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞)
    (M : ℝ) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) : MemLp (fun x => f x) p μ :=
  ⟨Lp.aestronglyMeasurable f,
    (eLpNorm_le_of_ae_norm_bound f p hp hptop M hM).trans_lt
      (lt_top_iff_ne_top.mpr (interpolation_bound_ne_top p hp hptop M ‖f‖))⟩

/-- The concrete Lp vector obtained from a bounded L1 function has the usual
interpolation norm estimate. -/
theorem norm_toLp_le_of_ae_norm_bound (f : Lp E 1 μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞) [Fact (1 ≤ p)]
    (M : ℝ) (hMnonneg : 0 ≤ M) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M)
    (hf : MemLp (fun x => f x) p μ) :
    ‖hf.toLp (fun x => f x)‖ ≤ M ^ (1 - 1 / p.toReal) * ‖f‖ ^ (1 / p.toReal) := by
  rw [Lp.norm_toLp]
  have h := ENNReal.toReal_mono (interpolation_bound_ne_top p hp hptop M ‖f‖)
    (eLpNorm_le_of_ae_norm_bound f p hp hptop M hM)
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hMnonneg, ENNReal.toReal_ofReal (norm_nonneg f)] using h

end PL1.LpInterpolation
