import ThesisCommon.Analysis.LpHaarDyadicMean

/-! Pointwise formulas and oscillation estimates for actual dyadic averages. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon

theorem lpHaarNormalizedIntegral_sub_le {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    {f : α → 𝕜} (hf : Integrable f μ) (c : 𝕜) (ε : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖f x - c‖ ≤ ε) :
    ‖(μ.real univ : 𝕜)⁻¹ * ∫ x, f x ∂μ - c‖ ≤ ε := by
  have hm : 0 < μ.real univ := ENNReal.toReal_pos hμ (measure_ne_top μ univ)
  have hm' : (μ.real univ : 𝕜) ≠ 0 := by exact_mod_cast hm.ne'
  have heq : (μ.real univ : 𝕜)⁻¹ * ∫ x, f x ∂μ - c =
      (μ.real univ : 𝕜)⁻¹ * ∫ x, f x - c ∂μ := by
    rw [integral_sub hf (integrable_const c), integral_const,
      Algebra.smul_def, RCLike.algebraMap_eq_ofReal, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hm', one_mul]
  rw [heq, norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hm]
  calc
    _ ≤ (μ.real univ)⁻¹ * (ε * μ.real univ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hb) (inv_nonneg.mpr hm.le)
    _ = ε := by field_simp

theorem lpHaarMean_coe {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]
    (hp : p ≠ ∞) (f : Lp 𝕜 p μ) :
    lpHaarMean hp f =ᵐ[μ] fun _ => (μ.real univ : 𝕜)⁻¹ * ∫ x, f x ∂μ := by
  rw [lpHaarMean_apply]
  exact Lp.coeFn_const p μ _

theorem lpHaarDyadicMean_coe (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (f : IntervalLp 𝕜 p) (k : Fin (2 ^ n)) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ lpHaarCell n k →
      lpHaarDyadicMean 𝕜 p hp n f x =
        ((intervalLpDyadicRadius n : ℝ) : 𝕜)⁻¹ *
          ∫ y in lpHaarCell n k, f y ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have h : lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarDyadicMean 𝕜 p hp n f)
      =ᵐ[μ.restrict (lpHaarCell n k)] fun _ =>
        ((μ.restrict (lpHaarCell n k)).real univ : 𝕜)⁻¹ *
          ∫ y, lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) f y ∂(μ.restrict (lpHaarCell n k)) := by
    rw [lpHaarDyadicMean_coordinate]
    exact lpHaarMean_coe hp _
  have h' := (lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n k)
    (lpHaarDyadicMean 𝕜 p hp n f)).symm.trans h
  have hm : (μ.restrict (lpHaarCell n k)).real univ = intervalLpDyadicRadius n := by
    rw [measureReal_def, Measure.restrict_apply_univ, lpHaarCell_measure n k k.isLt,
      ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]
  rw [hm, integral_congr_ae (lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n k) f)] at h'
  exact (ae_restrict_iff' measurableSet_Ioc).mp h'

theorem lpHaarCell_dist_le (n k : ℕ) {x y : ℝ}
    (hx : x ∈ lpHaarCell n k) (hy : y ∈ lpHaarCell n k) :
    dist x y ≤ intervalLpDyadicRadius n := by
  rw [Real.dist_eq, abs_le]
  constructor <;> dsimp [lpHaarCell] at hx hy <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

end ThesisCommon
