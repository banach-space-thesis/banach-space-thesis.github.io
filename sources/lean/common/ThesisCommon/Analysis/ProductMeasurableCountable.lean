import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Tactic

/-! A jointly measurable function into a countably generated measurable space
depends on a countably generated sub-sigma-algebra of its first variable.
The ambient measurable space need not itself be countably generated. -/
noncomputable section
open Set MeasurableSpace MeasureTheory
namespace ThesisCommon
variable {X Y Z : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

omit mX in
theorem measurableSpace_prod_mono_left {m₁ m₂ : MeasurableSpace X} (h : m₁ ≤ m₂) :
    m₁.prod mY ≤ m₂.prod mY :=
  sup_le_sup (MeasurableSpace.comap_mono h) le_rfl

theorem exists_countable_left_generators_of_measurableSet {s : Set (X × Y)}
    (hs : MeasurableSet s) :
    ∃ C : Set (Set X), C.Countable ∧ (∀ t ∈ C, MeasurableSet t) ∧
      MeasurableSet[(generateFrom C).prod mY] s := by
  classical
  rw [← generateFrom_prod] at hs
  induction s, hs using MeasurableSpace.generateFrom_induction with
  | hC t ht =>
      rcases ht with ⟨a, ha, b, hb, rfl⟩
      refine ⟨{a}, countable_singleton a, ?_, ?_⟩
      · intro u hu
        simpa only [mem_singleton_iff.mp hu] using ha
      · exact (measurableSet_generateFrom (mem_singleton a)).prod hb
  | empty => exact ⟨∅, countable_empty, by simp,
      @MeasurableSet.empty (X × Y) ((generateFrom ∅).prod mY)⟩
  | compl t ht ih =>
      obtain ⟨C, hc, hm, htC⟩ := ih
      exact ⟨C, hc, hm, htC.compl⟩
  | iUnion s hs ih =>
      choose C hcount hmeas hsets using ih
      refine ⟨⋃ n, C n, countable_iUnion hcount, ?_, ?_⟩
      · intro t ht
        obtain ⟨n, hn⟩ := mem_iUnion.mp ht
        exact hmeas n t hn
      · apply MeasurableSet.iUnion
        intro n
        exact measurableSpace_prod_mono_left
          (generateFrom_mono (subset_iUnion C n)) _ (hsets n)

/-- The countable generators can depend on the function. No countability or
separation assumption is imposed on either factor of the original product. -/
theorem exists_countable_left_generators_of_measurable [mZ : MeasurableSpace Z]
    [CountablyGenerated Z] {f : X × Y → Z} (hf : Measurable f) :
    ∃ C : Set (Set X), C.Countable ∧ (∀ t ∈ C, MeasurableSet t) ∧
      @Measurable (X × Y) Z ((generateFrom C).prod mY) mZ f := by
  classical
  let B := countableGeneratingSet Z
  letI : Countable B := countable_countableGeneratingSet.to_subtype
  have hex (b : B) := exists_countable_left_generators_of_measurableSet
    (hf (measurableSet_countableGeneratingSet b.property))
  choose C hcount hmeas hsets using hex
  refine ⟨⋃ b, C b, countable_iUnion hcount, ?_, ?_⟩
  · intro t ht
    obtain ⟨b, hb⟩ := mem_iUnion.mp ht
    exact hmeas b t hb
  · rw [← generateFrom_countableGeneratingSet (α := Z)]
    apply @measurable_generateFrom (X × Y) Z ((generateFrom (⋃ b, C b)).prod mY)
    intro b hb
    exact measurableSpace_prod_mono_left
      (generateFrom_mono (subset_iUnion C ⟨b, hb⟩)) _ (hsets ⟨b, hb⟩)

end ThesisCommon
