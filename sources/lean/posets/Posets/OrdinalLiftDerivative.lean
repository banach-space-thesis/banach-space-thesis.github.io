import ThesisCommon.Analysis.OrdinalDerived
import Mathlib.Topology.Maps.Proper.Basic

/-! A relative Cantor--Bendixson derivative for a continuous map. A point
survives when every neighborhood contains a point with a different image.
This records precisely the separation needed for a lifted ordinal copy. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def ordinalLiftDerivative (f : X → Y) (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∀ U : Set X, IsOpen U → x ∈ U →
    ∃ z ∈ A, z ∈ U ∧ f z ≠ f x}

theorem ordinalLiftDerivative_subset (f : X → Y) (A : Set X) :
    ordinalLiftDerivative f A ⊆ A := fun _ hx => hx.1

theorem ordinalLiftDerivative_mono (f : X → Y) {A B : Set X} (hAB : A ⊆ B) :
    ordinalLiftDerivative f A ⊆ ordinalLiftDerivative f B := by
  intro x hx
  refine ⟨hAB hx.1, ?_⟩
  intro U hU hxU
  obtain ⟨z, hz, hzU, hne⟩ := hx.2 U hU hxU
  exact ⟨z, hAB hz, hzU, hne⟩

theorem isClosed_ordinalLiftDerivative (f : X → Y) {A : Set X} (hA : IsClosed A) :
    IsClosed (ordinalLiftDerivative f A) := by
  classical
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  by_cases hxA : x ∈ A
  · have hno : ¬ ∀ U : Set X, IsOpen U → x ∈ U →
        ∃ z ∈ A, z ∈ U ∧ f z ≠ f x := fun h => hx ⟨hxA, h⟩
    push_neg at hno
    obtain ⟨U, hU, hxU, hconst⟩ := hno
    refine ⟨U, ?_, hU, hxU⟩
    intro y hy hdy
    obtain ⟨z, hzA, hzU, hne⟩ := hdy.2 U hU hy
    exact hne ((hconst z hzA hzU).trans (hconst y hdy.1 hy).symm)
  · exact ⟨Aᶜ, fun _ hy hdy => hy hdy.1, hA.isOpen_compl, hxA⟩

theorem ordinalLiftDerivative_image_subset (f : X → Y) (hf : Continuous f) (A : Set X) :
    f '' ordinalLiftDerivative f A ⊆ derivedSet (f '' A) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_derivedSet, accPt_iff_nhds]
  intro V hV
  obtain ⟨W, hWV, hW, hxW⟩ := mem_nhds_iff.mp hV
  obtain ⟨z, hzA, hzW, hne⟩ := hx.2 (f ⁻¹' W) (hW.preimage hf) hxW
  exact ⟨f z, ⟨hWV hzW, mem_image_of_mem f hzA⟩, hne⟩

theorem ordinalLiftDerivative_image [T2Space Y] (f : X → Y) (hf : Continuous f)
    {A : Set X} (hA : IsCompact A) :
    f '' ordinalLiftDerivative f A = derivedSet (f '' A) := by
  classical
  apply Subset.antisymm (ordinalLiftDerivative_image_subset f hf A)
  intro y hy
  by_contra hn
  have hw (x : {x : X // x ∈ A ∧ f x = y}) :
      ∃ U : Set X, IsOpen U ∧ x.val ∈ U ∧ ∀ z ∈ A, z ∈ U → f z = y := by
    have hd : x.val ∉ ordinalLiftDerivative f A := fun h => hn ⟨x.val, h, x.property.2⟩
    have hno : ¬ ∀ U : Set X, IsOpen U → x.val ∈ U →
        ∃ z ∈ A, z ∈ U ∧ f z ≠ f x.val := fun h => hd ⟨x.property.1, h⟩
    push_neg at hno
    obtain ⟨U, hU, hxU, hh⟩ := hno
    exact ⟨U, hU, hxU, fun z hz hzU => (hh z hz hzU).trans x.property.2⟩
  choose U hU hxU hconst using hw
  let W := ⋃ x, U x
  have hW : IsOpen W := isOpen_iUnion hU
  have hyW : y ∉ f '' (A \ W) := by
    rintro ⟨x, hx, he⟩
    exact hx.2 (mem_iUnion.mpr ⟨⟨x, hx.1, he⟩, hxU ⟨x, hx.1, he⟩⟩)
  have hclosed : IsClosed (f '' (A \ W)) := ((hA.diff hW).image hf).isClosed
  have hnbhd : (f '' (A \ W))ᶜ ∈ 𝓝 y := hclosed.isOpen_compl.mem_nhds hyW
  obtain ⟨z, ⟨hzW, a, ha, rfl⟩, hne⟩ := (accPt_iff_nhds.mp hy) _ hnbhd
  apply hzW
  refine ⟨a, ⟨ha, ?_⟩, rfl⟩
  intro haW
  obtain ⟨x, hx⟩ := mem_iUnion.mp haW
  exact hne (hconst x a ha hx)

end Posets
