import ThesisCommon.Analysis.L1UniformIntegrableCutSequence
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Real and complex L1 isometries preserve a.e. disjointness. Equality in
both triangle inequalities forces the two scalar values to be disjoint,
by the scalar parallelogram identity. No positivity of the isometry is assumed. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem ae_norm_add_of_lOne_norm_add_eq (f g : Lp 𝕜 1 μ)
    (h : ‖f + g‖ = ‖f‖ + ‖g‖) :
    ∀ᵐ x ∂μ, ‖f x + g x‖ = ‖f x‖ + ‖g x‖ := by
  have hf := L1.integrable_coeFn f
  have hg := L1.integrable_coeFn g
  have hadd : (∫ x, ‖f x + g x‖ ∂μ) = ‖f + g‖ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [hx, Pi.add_apply]
  have hint : Integrable (fun x => ‖f x‖ + ‖g x‖ - ‖f x + g x‖) μ :=
    (hf.norm.add hg.norm).sub (hf.add hg).norm
  have hz : (∫ x, (‖f x‖ + ‖g x‖ - ‖f x + g x‖) ∂μ) = 0 := by
    have hs := integral_sub (hf.norm.add hg.norm) (hf.add hg).norm
    have ha := integral_add hf.norm hg.norm
    simp only [Pi.add_apply] at hs ha
    rw [hs, ha, hadd, ← L1.norm_eq_integral_norm, ← L1.norm_eq_integral_norm, h]
    ring
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x => sub_nonneg.mpr (norm_add_le (f x) (g x))) hint).mp hz
  filter_upwards [hae] with x hx
  exact (sub_eq_zero.mp hx).symm

theorem ae_disjoint_of_lOne_norm_add_sub_eq (f g : Lp 𝕜 1 μ)
    (ha : ‖f + g‖ = ‖f‖ + ‖g‖) (hs : ‖f - g‖ = ‖f‖ + ‖g‖) :
    ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0 := by
  have hneg : ‖f + -g‖ = ‖f‖ + ‖-g‖ := by simpa only [← sub_eq_add_neg, norm_neg] using hs
  filter_upwards [ae_norm_add_of_lOne_norm_add_eq f g ha,
    ae_norm_add_of_lOne_norm_add_eq f (-g) hneg, Lp.coeFn_neg g] with x hax hsx hnegx
  have hsx : ‖f x - g x‖ = ‖f x‖ + ‖g x‖ := by
    simpa only [hnegx, Pi.neg_apply, norm_neg, ← sub_eq_add_neg] using hsx
  have hpar := parallelogram_law_with_norm 𝕜 (f x) (g x)
  rw [hax, hsx] at hpar
  have hprod : ‖f x‖ * ‖g x‖ = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hf | hg
  · exact Or.inl (norm_eq_zero.mp hf)
  · exact Or.inr (norm_eq_zero.mp hg)

theorem lOne_isometry_preserves_ae_disjoint
    (J : Lp 𝕜 1 μ →ₗᵢ[𝕜] Lp 𝕜 1 ν) (f g : Lp 𝕜 1 μ)
    (hd : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) :
    ∀ᵐ y ∂ν, J f y = 0 ∨ J g y = 0 := by
  apply ae_disjoint_of_lOne_norm_add_sub_eq
  · rw [← map_add, J.norm_map, J.norm_map, J.norm_map]
    exact norm_lOne_add_of_ae_disjoint f g hd
  · rw [← map_sub, J.norm_map, J.norm_map, J.norm_map]
    have hdn : ∀ᵐ x ∂μ, f x = 0 ∨ (-g) x = 0 := by
      filter_upwards [hd, Lp.coeFn_neg g] with x hx he
      rcases hx with hf | hg
      · exact Or.inl hf
      · exact Or.inr (he.trans (by simp only [Pi.neg_apply, hg, neg_zero]))
    simpa only [← sub_eq_add_neg, norm_neg] using norm_lOne_add_of_ae_disjoint f (-g) hdn

end ThesisCommon
