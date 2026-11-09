import NonCalkinAlgebra.EllOneSeparable
import Mathlib.Topology.Sets.Opens
import Mathlib.SetTheory.Cardinal.Continuum

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open TopologicalSpace
universe u

variable {E : Type u} [TopologicalSpace E] [SecondCountableTopology E]

/-- An open set is coded by the natural-number codes of basis elements
contained in it. This uses an actual countable topological basis. -/
def openSetCode (U : Opens E) : Set ℕ :=
  {n | ∃ b : countableBasis E, Encodable.encode b = n ∧ (b.val : Set E) ⊆ U}

theorem openSetCode_injective : Function.Injective (openSetCode (E := E)) := by
  classical
  have hle : ∀ U V : Opens E, openSetCode U ⊆ openSetCode V → U ≤ V := by
    intro U V hUV x hx
    obtain ⟨b, hb, hxb, hsub⟩ :=
      (isBasis_countableBasis E).exists_subset_of_mem_open hx U.isOpen
    let b' : countableBasis E := ⟨b, hb⟩
    have hcode : Encodable.encode b' ∈ openSetCode U := ⟨b', rfl, hsub⟩
    obtain ⟨c, hc, hcsub⟩ := hUV hcode
    have hcb : c = b' := Encodable.encode_injective hc
    subst c
    exact hcsub hxb
  intro U V hUV
  exact le_antisymm (hle U V (fun _ hn => hUV ▸ hn))
    (hle V U (fun _ hn => hUV.symm ▸ hn))

/-- A closed linear subspace is determined by the open complement, hence
by a subset of ℕ. -/
def closedEllOneSubspaceCode (N : ClosedEllOneSubspace) : Set ℕ :=
  openSetCode ⟨(N.val : Set ComplexEllOne)ᶜ, N.property.isOpen_compl⟩

theorem closedEllOneSubspaceCode_injective :
    Function.Injective closedEllOneSubspaceCode := by
  intro N M h
  have hopen := openSetCode_injective h
  have hc : (N.val : Set ComplexEllOne)ᶜ = (M.val : Set ComplexEllOne)ᶜ :=
    congrArg (fun U : Opens ComplexEllOne => (U : Set ComplexEllOne)) hopen
  apply Subtype.ext
  apply SetLike.coe_injective
  exact compl_injective hc

theorem cardinal_closedEllOneSubspace_le_continuum :
    Cardinal.mk ClosedEllOneSubspace ≤ Cardinal.continuum := by
  simpa only [Cardinal.mk_set_nat, Cardinal.lift_id] using
    Cardinal.mk_le_of_injective closedEllOneSubspaceCode_injective

end NonCalkinAlgebra
