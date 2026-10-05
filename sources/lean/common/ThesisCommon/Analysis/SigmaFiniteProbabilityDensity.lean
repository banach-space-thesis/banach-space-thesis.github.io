import ThesisCommon.Analysis.L1DensityEquiv

/-! Bounded positive densities giving finite and probability measures.
Boundedness permits reuse of arbitrary finite-measure partition pieces. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X]

theorem exists_positive_bounded_finite_density (μ : Measure X) [SigmaFinite μ] :
    ∃ g : X → ℝ≥0, Measurable g ∧ (∀ᵐ x ∂μ, 0 < g x) ∧
      (∀ x, g x ≤ 1) ∧ IsFiniteMeasure (μ.withDensity (fun x => (g x : ℝ≥0∞))) := by
  obtain ⟨g, hg, hpos, hfin⟩ := exists_positive_finite_density μ
  letI := hfin
  let r : X → ℝ≥0 := fun x => min (g x) 1
  refine ⟨r, hg.min measurable_const, hpos.mono (fun x hx => lt_min hx zero_lt_one),
    fun x => min_le_right _ _, ?_⟩
  apply isFiniteMeasure_of_le (μ.withDensity (fun x => (g x : ℝ≥0∞)))
  apply withDensity_mono
  exact Eventually.of_forall fun x => ENNReal.coe_le_coe.mpr (min_le_left (g x) 1)

theorem positive_density_measure_ne_zero {μ : Measure X} {g : X → ℝ≥0}
    (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x) (hμ : μ ≠ 0) :
    μ.withDensity (fun x => (g x : ℝ≥0∞)) ≠ 0 := by
  intro hzero
  have hfalse : ∀ᵐ x ∂μ, False := (ae_withDensity_coe_iff_of_pos hg hpos).mp (by simp [hzero])
  exact hμ (Measure.measure_univ_eq_zero.mp (by simpa only [ae_iff, not_false_eq_true,
    Set.setOf_true] using hfalse))

theorem exists_positive_bounded_probability_density (μ : Measure X) [SigmaFinite μ]
    (hμ : μ ≠ 0) :
    ∃ (g : X → ℝ≥0) (C : ℝ≥0), Measurable g ∧ (∀ᵐ x ∂μ, 0 < g x) ∧
      (∀ x, g x ≤ C) ∧ (μ.withDensity (fun x => (g x : ℝ≥0∞))) univ = 1 := by
  obtain ⟨g, hg, hpos, hbound, hfin⟩ := exists_positive_bounded_finite_density μ
  let ν := μ.withDensity (fun x => (g x : ℝ≥0∞))
  letI : IsFiniteMeasure ν := hfin
  have hν : ν univ ≠ 0 := Measure.measure_univ_eq_zero.not.mpr
    (positive_density_measure_ne_zero hg hpos hμ)
  let c : ℝ≥0 := (ν univ).toNNReal⁻¹
  have hc : 0 < c := inv_pos.mpr (ENNReal.toNNReal_pos hν (measure_ne_top ν univ))
  refine ⟨fun x => c * g x, c, measurable_const.mul hg,
    hpos.mono (fun x hx => mul_pos hc hx), fun x => ?_, ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbound x) (zero_le c)
  · have heq : μ.withDensity (fun x => ((c * g x : ℝ≥0) : ℝ≥0∞)) = (c : ℝ≥0∞) • ν := by
      simpa only [ENNReal.coe_mul, Pi.smul_apply, smul_eq_mul] using
        withDensity_smul (μ := μ) (c : ℝ≥0∞) hg.coe_nnreal_ennreal
    rw [heq, Measure.smul_apply, smul_eq_mul]
    change (((ν univ).toNNReal⁻¹ : ℝ≥0) : ℝ≥0∞) * ν univ = 1
    rw [ENNReal.coe_inv (ne_of_gt (ENNReal.toNNReal_pos hν (measure_ne_top ν univ))),
      ENNReal.coe_toNNReal (measure_ne_top ν univ)]
    exact ENNReal.inv_mul_cancel hν (measure_ne_top ν univ)

end ThesisCommon
