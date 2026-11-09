import BanachIsometric.PiolaAffineIntegral
import BanachIsometric.MollifiedBoundary
import BanachIsometric.SmoothJacobianLimit

/-!
# Actual affine homotopy invariance for Lipschitz endpoints

The smooth identity is proved by Piola and box divergence. We mollify the two
actual endpoints, preserve the lateral boundary condition using compact
separation, and pass both signed integrals to their actual Lipschitz limits.
There is no assumed degree, integral invariance, or derivative convergence.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal

theorem integral_signedJacobian_affine_eq_of_lipschitz {n : ℕ}
    {f₀ f₁ : PiolaSpace n → PiolaSpace n} {C₀ C₁ : ℝ≥0}
    (hf₀ : LipschitzWith C₀ f₀) (hf₁ : LipschitzWith C₁ f₁)
    {ψ : PiolaSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (a b : PiolaSpace n) (hab : a ≤ b)
    (hboundary : ∀ x ∈ piolaBoxBoundary a b, ∀ t : unitInterval,
      (1 - (t : ℝ)) • f₀ x + (t : ℝ) • f₁ x ∉ tsupport ψ) :
    (∫ x in Icc a b, (fderiv ℝ f₀ x).det * ψ (f₀ x)) =
      ∫ x in Icc a b, (fderiv ℝ f₁ x).det * ψ (f₁ x) := by
  let fn₀ : ℕ → PiolaSpace n → PiolaSpace n := fun k =>
    smoothBumpConvolution volume (shrinkingBump (PiolaSpace n) k) f₀
  let fn₁ : ℕ → PiolaSpace n → PiolaSpace n := fun k =>
    smoothBumpConvolution volume (shrinkingBump (PiolaSpace n) k) f₁
  have hs : IsCompact (Icc a b) := isCompact_Icc
  have havoid := eventually_mollified_affine_boundary_avoids_closed volume hf₀ hf₁
    (isCompact_piolaBoxBoundary a b) (isClosed_tsupport ψ) hboundary
  have heq : (fun k => ∫ x in Icc a b, (fderiv ℝ (fn₀ k) x).det * ψ (fn₀ k x)) =ᶠ[atTop]
      (fun k => ∫ x in Icc a b, (fderiv ℝ (fn₁ k) x).det * ψ (fn₁ k x)) := by
    filter_upwards [havoid] with k hk
    have hC₀ : ContDiff ℝ 2 (fn₀ k) :=
      (contDiff_smoothBumpConvolution volume _ hf₀).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hC₁ : ContDiff ℝ 2 (fn₁ k) :=
      (contDiff_smoothBumpConvolution volume _ hf₁).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    apply integral_signedJacobian_affine_eq hC₀ hC₁ hψ a b hab
    intro x hx t
    by_contra hn
    exact hk x hx t (subset_tsupport ψ hn)
  have ht₀ := tendsto_integral_signedJacobian_smoothBumpConvolution volume hf₀ hs hψ.continuous
  have ht₁ := tendsto_integral_signedJacobian_smoothBumpConvolution volume hf₁ hs hψ.continuous
  exact tendsto_nhds_unique ht₀ (ht₁.congr' heq.symm)

end BanachIsometric
