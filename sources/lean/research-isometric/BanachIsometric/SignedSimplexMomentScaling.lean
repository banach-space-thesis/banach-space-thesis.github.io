import BanachIsometric.SignedSimplexChainMoments
import BanachIsometric.LipschitzConeNaturality

/-! The weighted count of a scaled Lipschitz chain scales by the dimension
plus the weight degree, using the signed Jacobian of each simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open MeasureTheory
open scoped NNReal Topology

def simplexScalarMap (n : ℕ) (a : ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  a • ContinuousLinearMap.id ℝ (Fin n → ℝ)

theorem rawSignedSimplexMoment_scale (n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure]
    (a : ℝ) (k : ℕ) {g : (Fin n → ℝ) → ℝ} (hg : Continuous g)
    (hscale : ∀ x, g (a • x) = a ^ k * g x)
    (c : RawRationalChains (Fin n → ℝ) n) (hc : c ∈ rawLipschitzCarrier (Fin n → ℝ) n) :
    rawSignedSimplexMoment n μ g
        (rawChainMap (continuousLinearSingularMap (simplexScalarMap n a)) n c) =
      a ^ (n + k) * rawSignedSimplexMoment n μ g c := by
  let M := rawSignedSimplexMoment n μ g
  let A := M.comp (rawChainMap (continuousLinearSingularMap (simplexScalarMap n a)) n)
  let B := ((LinearMap.mul ℚ ℝ) (a ^ (n + k))).comp M
  have hsub : rawLipschitzCarrier (Fin n → ℝ) n ≤ LinearMap.ker (A - B) := by
    rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, ⟨K, hK⟩, rfl⟩
    change (A - B) (Finsupp.single σ 1) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    let T := simplexScalarMap n a
    let τ := (continuousLinearSingularMap T).comp σ
    have hτ : ∃ L : ℝ≥0, LipschitzWith L τ := ⟨_, T.lipschitz.comp hK⟩
    have hτe (x : signedSimplexDomain n) :
        (a • signedSimplexExtension n σ) x.val = τ ((signedSimplexCoordinates n).symm x) := by
      change a • signedSimplexExtension n σ x.val = a • σ ((signedSimplexCoordinates n).symm x)
      rw [(signedSimplexExtension_spec n σ ⟨K, hK⟩).2 x]
    have hA : A (Finsupp.single σ 1) = ∫ y, signedSimplexCount n τ y * g y ∂μ := by
      simp [A, M, τ, T, rawChainMap, rawSignedSimplexMoment]
    have hB : B (Finsupp.single σ 1) = a ^ (n + k) * ∫ y, signedSimplexCount n σ y * g y ∂μ := by
      simp [B, M, rawSignedSimplexMoment]
    rw [hA, hB, integral_signedSimplexCount_of_extension n μ τ hτ _ hτe hg,
      integral_signedSimplexCount n μ σ ⟨K, hK⟩ hg, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [fderiv_const_smul_of_field, Pi.smul_apply]
    rw [hscale, pow_add]
    have hdet : (a • fderiv ℝ (signedSimplexExtension n σ) x).det =
        a ^ n * (fderiv ℝ (signedSimplexExtension n σ) x).det := by
      change (a • (fderiv ℝ (signedSimplexExtension n σ) x).toLinearMap).det = _
      rw [LinearMap.det_smul]
      simp
    rw [hdet]
    ring
  have hz := hsub hc
  change (A - B) c = 0 at hz
  exact sub_eq_zero.mp hz

end BanachIsometric.SingularPrism
