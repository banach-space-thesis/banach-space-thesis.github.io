import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Uniform integrability is inherited by an a.e. norm-dominated family,
including families taking values in different normed spaces. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {I Y E F : Type*} [MeasurableSpace Y]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {ν : Measure Y} {p : ENNReal} {f : I → Y → E} {g : I → Y → F}

theorem uniformIntegrable_of_ae_norm_le (hf : UniformIntegrable f p ν)
    (hg : ∀ i, AEStronglyMeasurable (g i) ν)
    (hgf : ∀ i, ∀ᵐ y ∂ν, ‖g i y‖ ≤ ‖f i y‖) : UniformIntegrable g p ν := by
  refine ⟨hg, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hfδ⟩ := hf.2.1 hε
    refine ⟨δ, hδ, fun i s hs hνs => ?_⟩
    apply (eLpNorm_mono_ae ?_).trans (hfδ i s hs hνs)
    filter_upwards [hgf i] with y hy
    by_cases hys : y ∈ s <;> simp [hys, hy]
  · obtain ⟨C, hC⟩ := hf.2.2
    exact ⟨C, fun i => (eLpNorm_mono_ae (hgf i)).trans (hC i)⟩

end ThesisCommon
