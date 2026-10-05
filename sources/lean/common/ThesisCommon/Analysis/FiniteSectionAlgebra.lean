import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Tactic

/-! A concrete algebra of product sets with finitely many measurable input
sections. Simple functions encode the finite membership patterns used in the
rectangle-content construction; no pointwise choice of an L1 representative
depending on infinitely many parameters is involved. -/
noncomputable section
open MeasureTheory Set
local infixr:25 " →ₛ " => MeasureTheory.SimpleFunc
namespace ThesisCommon
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

abbrev MeasurableSubset (X : Type*) [MeasurableSpace X] := {s : Set X // MeasurableSet s}

def sectionSet (q : Y →ₛ MeasurableSubset X) : Set (X × Y) :=
  {z | z.1 ∈ (q z.2).val}

theorem sectionSet_measurable (q : Y →ₛ MeasurableSubset X) : MeasurableSet (sectionSet q) := by
  classical
  have heq : sectionSet q = ⋃ a ∈ q.range, a.val ×ˢ (q ⁻¹' {a}) := by
    ext z
    simp only [sectionSet, mem_setOf_eq, mem_iUnion, mem_prod, mem_preimage, mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨q z.2, q.mem_range_self z.2, hz, rfl⟩
    · rintro ⟨a, _, ha, heq⟩
      simpa only [heq] using ha
  rw [heq]
  exact q.range.finite_toSet.measurableSet_biUnion (fun a _ => a.property.prod (q.measurableSet_fiber a))

def finiteSectionAlgebra (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] :
    Set (Set (X × Y)) := Set.range (sectionSet (X := X) (Y := Y))

theorem finiteSectionAlgebra_measurable {s : Set (X × Y)} (hs : s ∈ finiteSectionAlgebra X Y) :
    MeasurableSet s := by
  obtain ⟨q, rfl⟩ := hs
  exact sectionSet_measurable q

theorem finiteSectionAlgebra_isSetAlgebra : IsSetAlgebra (finiteSectionAlgebra X Y) where
  empty_mem := ⟨SimpleFunc.const Y ⟨∅, MeasurableSet.empty⟩, by ext z; simp [sectionSet]⟩
  compl_mem := by
    rintro s ⟨q, rfl⟩
    refine ⟨q.map (fun a => ⟨a.valᶜ, a.property.compl⟩), ?_⟩
    ext z
    simp [sectionSet]
  union_mem := by
    rintro s t ⟨q, rfl⟩ ⟨r, rfl⟩
    refine ⟨(q.pair r).map (fun a => ⟨a.1.val ∪ a.2.val, a.1.property.union a.2.property⟩), ?_⟩
    ext z
    simp [sectionSet]

theorem prod_mem_finiteSectionAlgebra {a : Set X} {b : Set Y}
    (ha : MeasurableSet a) (hb : MeasurableSet b) : a ×ˢ b ∈ finiteSectionAlgebra X Y := by
  classical
  refine ⟨SimpleFunc.piecewise b hb (SimpleFunc.const Y ⟨a, ha⟩)
    (SimpleFunc.const Y ⟨∅, MeasurableSet.empty⟩), ?_⟩
  ext z
  by_cases hz : z.2 ∈ b <;> simp [sectionSet, SimpleFunc.piecewise_apply, hz]

theorem generateFrom_finiteSectionAlgebra :
    MeasurableSpace.generateFrom (finiteSectionAlgebra X Y) = mX.prod mY := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le (fun _ hs => finiteSectionAlgebra_measurable hs)
  · change (inferInstance : MeasurableSpace (X × Y)) ≤ _
    rw [← generateFrom_prod]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact prod_mem_finiteSectionAlgebra ha hb

/-- The section encoder is determined by the product set, including empty
factors. Different encodings cannot change the content constructed later. -/
theorem sectionSet_injective : Function.Injective (sectionSet (X := X) (Y := Y)) := by
  intro q r heq
  apply SimpleFunc.ext
  intro y
  apply Subtype.ext
  ext x
  exact Set.ext_iff.mp heq (x, y)

end ThesisCommon
