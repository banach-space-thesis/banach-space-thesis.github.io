import BanachIsometric.LipschitzSignedArea
import BanachIsometric.SignedFiberNormalization

/-!
# Actual orientation normalisation of the signed integral

The signed area formula and the actual linear-equivalence fiber count give
the determinant sign on every target test supported inside the image source.
This proves the normalisation needed by the analytic index construction.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem integral_signedJacobian_linearEquiv_of_support_subset
    (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃L[ℝ] E)
    {S : Set E} (hS : IsCompact S) {ψ : E → ℝ} (hψ : Continuous ψ)
    (hsupp : Function.support ψ ⊆ A '' S) :
    (∫ x in S, (fderiv ℝ (A : E → E) x).det * ψ (A x) ∂μ) =
      (SignType.sign (A : E →L[ℝ] E).det : ℝ) * ∫ y, ψ y ∂μ := by
  classical
  have hder : fderiv ℝ (A : E → E) = fun _ => (A : E →L[ℝ] E) := by
    funext x
    exact A.fderiv
  rw [← integral_signedFiberCount_of_compact_lipschitz μ A.lipschitz hS hψ]
  calc
    (∫ y, (signedFiberCount A (fderiv ℝ (A : E → E)) S y : ℝ) * ψ y ∂μ) =
        ∫ y, (SignType.sign (A : E →L[ℝ] E).det : ℝ) * ψ y ∂μ := by
      apply integral_congr_ae
      apply ae_of_all
      intro y
      change (signedFiberCount A (fderiv ℝ (A : E → E)) S y : ℝ) * ψ y =
        (SignType.sign (A : E →L[ℝ] E).det : ℝ) * ψ y
      by_cases hy : ψ y = 0
      · simp only [hy, mul_zero]
      · have hmem : A.symm y ∈ S := by
          obtain ⟨x, hx, hxy⟩ := hsupp hy
          simpa only [← hxy, A.symm_apply_apply] using hx
        rw [hder, signedFiberCount_linearEquiv, if_pos hmem, SignType.intCast_cast]
    _ = (SignType.sign (A : E →L[ℝ] E).det : ℝ) * ∫ y, ψ y ∂μ := integral_const_mul _ _

theorem integral_signedJacobian_id_of_support_subset
    (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E} (hS : IsCompact S)
    {ψ : E → ℝ} (hψ : Continuous ψ) (hsupp : Function.support ψ ⊆ S) :
    (∫ x in S, (fderiv ℝ (id : E → E) x).det * ψ x ∂μ) = ∫ y, ψ y ∂μ := by
  have hd : (ContinuousLinearMap.id ℝ E).det = 1 := by
    change LinearMap.det (1 : Module.End ℝ E) = 1
    exact map_one (LinearMap.det : Module.End ℝ E →* ℝ)
  simpa [hd] using integral_signedJacobian_linearEquiv_of_support_subset μ
    (ContinuousLinearEquiv.refl ℝ E) hS hψ (by simpa using hsupp)

end BanachIsometric
