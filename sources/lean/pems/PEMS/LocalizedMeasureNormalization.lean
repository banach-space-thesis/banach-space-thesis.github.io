import PEMS.MeasureDefinitions
import ThesisCommon.Analysis.LocalizedProbabilityDensity
import ThesisCommon.Analysis.L1DensityMultipliers

/-! Proposition 3.10: localized sigma-finite to finite normalization.
The density is bounded, so the original strict-localization partition still works.
The zero-measure case is included, with mass zero instead of mass one. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal NNReal
namespace PEMS
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strictlyLocalizable_withDensity_of_bound (hμ : StrictlyLocalizable μ)
    (g : X → ℝ≥0) (C : ℝ≥0) (hbound : ∀ x, g x ≤ C) :
    StrictlyLocalizable (μ.withDensity (fun x => (g x : ℝ≥0∞))) := by
  obtain ⟨parts, hfinite, hdisj, hcover, hlocal, hsum⟩ := hμ
  have hle : μ.withDensity (fun x => (g x : ℝ≥0∞)) ≤ (C : ℝ≥0∞) • μ := by
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun x => ENNReal.coe_le_coe.mpr (hbound x))
  have heq : μ = Measure.sum (fun B : parts => μ.restrict B.val) := by
    ext A hA
    rw [Measure.sum_apply _ hA]
    simpa only [Measure.restrict_apply hA] using hsum A hA
  refine ⟨parts, ?_, hdisj, hcover, hlocal, ?_⟩
  · intro A hA
    refine ⟨(hfinite A hA).1, (hle A).trans_lt ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hfinite A hA).2
  · intro A hA
    calc
      (μ.withDensity (fun x => (g x : ℝ≥0∞))) A =
          (Measure.sum (fun B : parts => (μ.restrict B.val).withDensity
            (fun x => (g x : ℝ≥0∞)))) A := by
        rw [← withDensity_sum, ← heq]
      _ = ∑' B : parts, (μ.withDensity (fun x => (g x : ℝ≥0∞))) (A ∩ B.val) := by
        rw [Measure.sum_apply _ hA]
        congr 1
        funext B
        rw [← restrict_withDensity (hfinite B.val B.property).1,
          Measure.restrict_apply hA]

theorem exists_strictlyLocalizable_normalization (hμ : StrictlyLocalizable μ)
    (s : Set X) (hs : MeasurableSet s) [SigmaFinite (μ.restrict s)] :
    ∃ (g : X → ℝ≥0) (C : ℝ≥0), Measurable g ∧ (∀ᵐ x ∂μ, 0 < g x) ∧
      (∀ x, g x ≤ C) ∧ StrictlyLocalizable (μ.withDensity (fun x => (g x : ℝ≥0∞))) ∧
      (μ.withDensity (fun x => (g x : ℝ≥0∞))).restrict sᶜ = μ.restrict sᶜ ∧
      (μ.withDensity (fun x => (g x : ℝ≥0∞))) s < ⊤ ∧
      (μ s ≠ 0 → (μ.withDensity (fun x => (g x : ℝ≥0∞))) s = 1) := by
  obtain ⟨g, C, hg, hpos, hbound, hout, hfin, hmass⟩ :=
    exists_localized_probability_density μ s hs
  exact ⟨g, C, hg, hpos, hbound, strictlyLocalizable_withDensity_of_bound hμ g C hbound,
    hout, hfin, hmass⟩

theorem localized_sigmaFinite_to_finite_lattice_isometry (hμ : StrictlyLocalizable μ)
    (s : Set X) (hs : MeasurableSet s) [SigmaFinite (μ.restrict s)] :
    ∃ (ν : Measure X) (Ψ : LOne ℝ μ ≃ₗᵢ[ℝ] LOne ℝ ν)
      (H : Lp ℝ ∞ μ → Lp ℝ ∞ ν),
      StrictlyLocalizable ν ∧ ν.restrict sᶜ = μ.restrict sᶜ ∧ ν s < ⊤ ∧
      (μ s ≠ 0 → ν s = 1) ∧
      (∀ f k, Ψ f ≤ Ψ k ↔ f ≤ k) ∧
      (∀ h, H h =ᵐ[ν] h) ∧
      (∀ h f, Ψ (h • f : LOne ℝ μ) = (H h • Ψ f : LOne ℝ ν)) := by
  obtain ⟨g, C, hg, hpos, hbound, hlocal, hout, hfin, hmass⟩ :=
    exists_strictlyLocalizable_normalization hμ s hs
  refine ⟨μ.withDensity (fun x => (g x : ℝ≥0∞)),
    (lOneWithDensityEquiv hg hpos).symm, lInfinityWithDensity g,
    hlocal, hout, hfin, hmass, ?_, lInfinityWithDensity_coe g, ?_⟩
  · intro f k
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (lOneWithDensityEquiv_le_iff hg hpos
        ((lOneWithDensityEquiv hg hpos).symm f) ((lOneWithDensityEquiv hg hpos).symm k)).symm
  · exact lOneWithDensityEquiv_symm_multiplier hg hpos

end PEMS
