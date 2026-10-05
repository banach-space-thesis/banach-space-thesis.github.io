import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-! Countable suprema of countably generated sigma algebras. -/
noncomputable section
open Set MeasurableSpace
namespace ThesisCommon

theorem countablyGenerated_iSup {X I : Type*} [Countable I]
    (m : I → MeasurableSpace X) (hm : ∀ i, @CountablyGenerated X (m i)) :
    @CountablyGenerated X (⨆ i, m i) := by
  classical
  have hex (i : I) : ∃ C : Set (Set X), C.Countable ∧ m i = generateFrom C :=
    (hm i).isCountablyGenerated
  choose C hcount hgen using hex
  refine @CountablyGenerated.mk X (⨆ i, m i) ⟨⋃ i, C i, countable_iUnion hcount, ?_⟩
  simp_rw [hgen, iSup_generateFrom]

theorem countablyGenerated_bot (X : Type*) : @CountablyGenerated X ⊥ :=
  @CountablyGenerated.mk X ⊥ ⟨∅, countable_empty, generateFrom_empty.symm⟩

end ThesisCommon
