import ThesisCommon.Analysis.IntervalAtomlessSampler
import ThesisCommon.Analysis.LpMeasureCoding
import ThesisCommon.Analysis.LebesgueLpTransport
import ThesisCommon.Analysis.IntervalL1SubtypeEquiv

/-! Genuine Lp isometries for atomless interval probability measures. The
injective measurable sampler generates the source sigma algebra, so the
already proved Lp coding construction is surjective. No full-support or
primariness hypothesis is used. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lebesgueLpMeasureCongr_coe {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (h : μ = ν) (f : Lp 𝕜 p μ) :
    (lebesgueLpMeasureCongr (𝕜 := 𝕜) h f : α → 𝕜) =ᵐ[μ] f := by
  subst ν
  exact Filter.EventuallyEq.rfl

variable (𝕜) (μ : Measure unitInterval) [IsProbabilityMeasure μ] [NoAtoms μ]

def intervalAtomlessLpEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p μ ≃ₗᵢ[𝕜] Lp 𝕜 p (volume : Measure unitInterval) :=
  (lebesgueLpMeasureCongr (intervalProbabilitySampler_map μ).symm).trans
    (lpComapEquiv volume (intervalProbabilitySampler μ)
      (intervalProbabilitySampler_measurable μ)
      (intervalProbabilitySampler_measurableEmbedding μ).comap_eq p)

theorem intervalAtomlessLpEquiv_coe (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp 𝕜 p μ) :
    (intervalAtomlessLpEquiv 𝕜 μ p f : unitInterval → 𝕜) =ᵐ[volume]
      f ∘ intervalProbabilitySampler μ := by
  have he := (intervalProbabilitySampler_measurePreserving μ).quasiMeasurePreserving.ae_eq_comp
    (lebesgueLpMeasureCongr_coe (intervalProbabilitySampler_map μ).symm f)
  exact (lpComapEquiv_coe volume (intervalProbabilitySampler μ)
    (intervalProbabilitySampler_measurable μ)
    (intervalProbabilitySampler_measurableEmbedding μ).comap_eq p _).trans he

def intervalAtomlessProbabilityL1Equiv :
    Lp 𝕜 1 μ ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
  (intervalAtomlessLpEquiv 𝕜 μ 1).trans (IntervalL1Subtype.equiv 𝕜)

theorem exists_intervalAtomlessProbabilityL1_equiv :
    Nonempty (Lp 𝕜 1 μ ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩) :=
  ⟨intervalAtomlessProbabilityL1Equiv 𝕜 μ⟩

end ThesisCommon
