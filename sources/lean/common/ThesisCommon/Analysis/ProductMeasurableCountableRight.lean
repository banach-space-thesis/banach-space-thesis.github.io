import ThesisCommon.Analysis.ProductMeasurableCountable

/-! A jointly measurable function with a countably generated target depends
on countably many measurable output sets. -/
noncomputable section
open Set MeasurableSpace MeasureTheory
namespace ThesisCommon
variable {X Y Z : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

omit mY in
theorem measurableSpace_prod_mono_right {m₁ m₂ : MeasurableSpace Y} (h : m₁ ≤ m₂) :
    mX.prod m₁ ≤ mX.prod m₂ :=
  sup_le_sup le_rfl (MeasurableSpace.comap_mono h)

theorem exists_countable_right_generators_of_measurable [mZ : MeasurableSpace Z]
    [CountablyGenerated Z] {f : X × Y → Z} (hf : Measurable f) :
    ∃ C : Set (Set Y), C.Countable ∧ (∀ t ∈ C, MeasurableSet t) ∧
      @Measurable (X × Y) Z (mX.prod (generateFrom C)) mZ f := by
  obtain ⟨C, hC, hm, hfC⟩ :=
    exists_countable_left_generators_of_measurable (hf.comp measurable_swap)
  refine ⟨C, hC, hm, ?_⟩
  exact hfC.comp (@measurable_swap X Y mX (generateFrom C))

end ThesisCommon
