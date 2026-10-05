import ThesisCommon.Analysis.SequenceSpaces

/-! Transport of genuine `Lp` classes along a measure-preserving measurable
equivalence, including transport across an equality of measures. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 α β E : Type*} [RCLike 𝕜] [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} {ν : Measure β}

theorem lebesgueLpTransport_surjective (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Function.Surjective (Lp.compMeasurePreservingₗᵢ (E := E) (p := p) 𝕜 e he) := by
  intro f
  let hi := MeasurePreserving.symm e he
  refine ⟨Lp.compMeasurePreserving e.symm hi f, Lp.ext ?_⟩
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving e.symm hi f) he,
    he.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hi)] with x h₁ h₂
  simpa only [Function.comp_apply, e.symm_apply_apply] using h₁.trans h₂

def lebesgueLpTransport (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Lp E p ν ≃ₗᵢ[𝕜] Lp E p μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ 𝕜 e he)
    (lebesgueLpTransport_surjective e he)

def lebesgueLpMeasureCongr {ν : Measure α} (h : μ = ν) :
    Lp E p μ ≃ₗᵢ[𝕜] Lp E p ν := by
  subst ν
  exact LinearIsometryEquiv.refl 𝕜 (Lp E p μ)

end ThesisCommon
