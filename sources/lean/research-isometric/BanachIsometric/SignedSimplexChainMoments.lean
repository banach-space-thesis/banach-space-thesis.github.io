import BanachIsometric.SignedSimplexExtensionIntegral
import BanachIsometric.SignedMultiplicityIntegrability

/-! Weighted signed counts add over a finite Lipschitz singular chain. The
integrals are genuine Bochner integrals with integrability proved for each
simplex in the actual support. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open MeasureTheory
open scoped NNReal

def rawSignedSimplexMoment (n : ℕ) (μ : Measure (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ) :
    RawRationalChains (Fin n → ℝ) n →ₗ[ℚ] ℝ :=
  Finsupp.linearCombination ℚ (fun σ => ∫ y, signedSimplexCount n σ y * g y ∂μ)

theorem integrable_signedSimplexCount_mul (n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure]
    (σ : RawSingularSimplex (Fin n → ℝ) n) (hσ : ∃ L : ℝ≥0, LipschitzWith L σ)
    {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    Integrable (fun y => signedSimplexCount n σ y * g y) μ := by
  obtain ⟨K, hK⟩ := (signedSimplexExtension_spec n σ hσ).1
  exact integrable_signedFiberCount_mul_of_compact_lipschitz μ hK (isCompact_signedSimplexDomain n) hg

theorem rawSignedSimplexMoment_eq_integral (n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure]
    (c : RawRationalChains (Fin n → ℝ) n) (hc : c ∈ rawLipschitzCarrier (Fin n → ℝ) n)
    {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    rawSignedSimplexMoment n μ g c = ∫ y, rawSignedSimplexCount n c y * g y ∂μ := by
  classical
  have hσ := (rawLipschitzCarrier_mem c).mp hc
  simp only [rawSignedSimplexMoment, rawSignedSimplexCount, Finsupp.linearCombination_apply, Finsupp.sum]
  have he (y : Fin n → ℝ) :
      (∑ σ ∈ c.support, c σ • signedSimplexCount n σ) y * g y =
        ∑ σ ∈ c.support, (c σ : ℝ) * (signedSimplexCount n σ y * g y) := by
    simp only [Finset.sum_apply, Pi.smul_apply, Rat.smul_def, Finset.sum_mul, mul_assoc]
  simp only [he]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [integral_const_mul, Rat.smul_def]
  · intro σ hσc
    exact (integrable_signedSimplexCount_mul n μ σ (hσ σ hσc) hg).const_mul _

end BanachIsometric.SingularPrism
