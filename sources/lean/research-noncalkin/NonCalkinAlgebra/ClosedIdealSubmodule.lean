import NonCalkinAlgebra.OneIdealCriterion
import Mathlib.Topology.Algebra.Algebra

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

def idealSubmodule (I : TwoSidedIdeal A) : Submodule ℂ A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := fun c a ha => twoSidedIdeal_smul_mem I ha c

@[simp] theorem mem_idealSubmodule (I : TwoSidedIdeal A) (a : A) :
    a ∈ idealSubmodule I ↔ a ∈ I := Iff.rfl

/-- A closed ideal in a closed subalgebra has closed image in the ambient algebra. -/
theorem idealSubmodule_map_isClosed (S : Subalgebra ℂ A) (hS : IsClosed (S : Set A))
    (I : TwoSidedIdeal S) (hI : IsClosed (I : Set S)) :
    IsClosed ((idealSubmodule I).map S.val.toLinearMap : Set A) := by
  change IsClosed (S.val '' (I : Set S))
  exact hS.isClosedMap_subtype_val _ hI

end NonCalkinAlgebra
