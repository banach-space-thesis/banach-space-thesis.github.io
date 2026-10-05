import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Closeds
import Mathlib.SetTheory.Cardinal.Continuum

/-! A second-countable space has at most continuum many closed subsets. -/
noncomputable section
open TopologicalSpace
namespace ThesisCommon
variable (Y : Type*) [TopologicalSpace Y] [SecondCountableTopology Y]

def closedSetBasisCode (s : Closeds Y) : Set (countableBasis Y) :=
  {b | b.val ⊆ (s : Set Y)ᶜ}

theorem closedSetBasisCode_injective : Function.Injective (closedSetBasisCode Y) := by
  intro s t h
  have hcomp : (s : Set Y)ᶜ = (t : Set Y)ᶜ := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨b, hb, hxb, hbs⟩ :=
        (isBasis_countableBasis Y).isOpen_iff.mp s.isClosed.isOpen_compl x hx
      have hbt : b ⊆ (t : Set Y)ᶜ := by
        have : (⟨b, hb⟩ : countableBasis Y) ∈ closedSetBasisCode Y s := hbs
        rw [h] at this
        exact this
      exact hbt hxb
    · intro x hx
      obtain ⟨b, hb, hxb, hbt⟩ :=
        (isBasis_countableBasis Y).isOpen_iff.mp t.isClosed.isOpen_compl x hx
      have hbs : b ⊆ (s : Set Y)ᶜ := by
        have : (⟨b, hb⟩ : countableBasis Y) ∈ closedSetBasisCode Y t := hbt
        rw [← h] at this
        exact this
      exact hbs hxb
  exact Closeds.ext (compl_injective hcomp)

theorem cardinal_closeds_le_continuum :
    Cardinal.mk (Closeds Y) ≤ Cardinal.continuum := by
  calc
    Cardinal.mk (Closeds Y) ≤ Cardinal.mk (Set (countableBasis Y)) :=
      Cardinal.mk_le_of_injective (closedSetBasisCode_injective Y)
    _ = 2 ^ Cardinal.mk (countableBasis Y) := Cardinal.mk_set
    _ ≤ 2 ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_left (by simp) Cardinal.mk_le_aleph0
    _ = Cardinal.continuum := rfl

end ThesisCommon
