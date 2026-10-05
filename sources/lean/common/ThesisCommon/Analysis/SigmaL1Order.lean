import ThesisCommon.Analysis.SigmaL1Partition

/-! Positivity is preserved and reflected by the actual measure-coproduct
L1 isometry. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)]

theorem sigmaL1ComponentEquiv_nonneg (μ : ∀ i, Measure (X i)) (i : I)
    (f : Lp ℝ 1 ((sigmaMeasure μ).restrict (sigmaMeasureFiber i))) :
    0 ≤ sigmaL1ComponentEquiv μ i f ↔ 0 ≤ f := by
  let hmp : MeasurePreserving (Sigma.mk i) (μ i) ((sigmaMeasure μ).restrict (sigmaMeasureFiber i)) :=
    ⟨measurable_sigmaMk i, (sigmaMeasure_restrict_fiber μ i).symm⟩
  have hc : sigmaL1ComponentEquiv μ i f =ᵐ[μ i] f ∘ Sigma.mk i :=
    Lp.coeFn_compMeasurePreserving f hmp
  rw [← Lp.coeFn_nonneg, ← Lp.coeFn_nonneg]
  have hmap : (∀ᵐ x ∂μ i, (0 : ℝ) ≤ f (Sigma.mk i x)) ↔
      ∀ᵐ y ∂(sigmaMeasure μ).restrict (sigmaMeasureFiber i), (0 : ℝ) ≤ f y := by
    have ha : (∀ᵐ y ∂(μ i).map (Sigma.mk i), (0 : ℝ) ≤ f y) ↔
        ∀ᵐ x ∂μ i, (0 : ℝ) ≤ f (Sigma.mk i x) :=
      ae_map_iff (measurable_sigmaMk i).aemeasurable
        (measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable)
    have he := congrArg (fun m : Measure (Sigma X) => ∀ᵐ y ∂m, (0 : ℝ) ≤ f y) hmp.map_eq
    exact ha.symm.trans (Iff.of_eq he)
  exact (Filter.eventually_congr (hc.mono (fun x hx => by rw [hx]; rfl))).trans hmap

theorem sigmaL1PartitionEquiv_nonneg (μ : ∀ i, Measure (X i))
    (f : Lp ℝ 1 (sigmaMeasure μ)) :
    (∀ i, 0 ≤ sigmaL1PartitionEquiv μ f i) ↔ 0 ≤ f := by
  simp only [sigmaL1PartitionEquiv_apply, sigmaL1ComponentEquiv_nonneg]
  constructor
  · intro h
    apply (Lp.coeFn_nonneg f).mp
    have hh : ∀ᵐ x ∂Measure.sum (fun i => (sigmaMeasure μ).restrict (sigmaMeasureFiber i)),
        (0 : ℝ) ≤ f x := by
      apply (Measure.ae_sum_iff' (measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable)).mpr
      intro i
      filter_upwards [(Lp.coeFn_nonneg _).mpr (h i), lebesgueLpRestrict_coe (𝕜 := ℝ) (sigmaMeasureFiber i) f]
        with x hx he
      simpa only [he] using hx
    simpa only [sigmaMeasure_sum_restrict] using hh
  · intro h i
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [ae_restrict_of_ae ((Lp.coeFn_nonneg f).mpr h),
      lebesgueLpRestrict_coe (𝕜 := ℝ) (sigmaMeasureFiber i) f] with x hx he
    simpa only [he] using hx

end ThesisCommon
