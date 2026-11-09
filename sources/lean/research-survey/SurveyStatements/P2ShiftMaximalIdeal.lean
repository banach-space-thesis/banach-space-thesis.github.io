import SurveyStatements.P2ShiftAlgebra
import SurveyStatements.P2BanachIdeals

/-! Choosing the actual maximal ideal for the source's second construction. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace SurveyStatements.P2
universe u
variable (Γ : Type u)

/-- The maximal proper closed two-sided ideal chosen by the source. -/
def shiftMaximalIdeal : TwoSidedIdeal (shiftAlgebra Γ) :=
  Classical.choose (exists_closed_isCoatom_twoSidedIdeal (R := shiftAlgebra Γ))

theorem shiftMaximalIdeal_isCoatom : IsCoatom (shiftMaximalIdeal Γ) :=
  (Classical.choose_spec (exists_closed_isCoatom_twoSidedIdeal (R := shiftAlgebra Γ))).1

theorem shiftMaximalIdeal_isClosed :
    IsClosed (shiftMaximalIdeal Γ : Set (shiftAlgebra Γ)) :=
  (Classical.choose_spec (exists_closed_isCoatom_twoSidedIdeal (R := shiftAlgebra Γ))).2

theorem shiftMaximalIdeal_ne_top : shiftMaximalIdeal Γ ≠ ⊤ :=
  (shiftMaximalIdeal_isCoatom Γ).ne_top

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- A two-sided ideal in a complex algebra is also a complex vector subspace. -/
def idealSubmodule (M : TwoSidedIdeal A) : Submodule ℂ A where
  carrier := M
  zero_mem' := M.zero_mem
  add_mem' := M.add_mem
  smul_mem' c x hx := by
    rw [Algebra.smul_def]
    exact M.mul_mem_left (algebraMap ℂ A c) x hx

@[simp] theorem mem_idealSubmodule (M : TwoSidedIdeal A) (x : A) :
    x ∈ idealSubmodule M ↔ x ∈ M := Iff.rfl

instance idealSubmodule_isClosed (M : TwoSidedIdeal A)
    [Fact (IsClosed (M : Set A))] : IsClosed (idealSubmodule M : Set A) := by
  change IsClosed (M : Set A)
  exact (inferInstance : Fact (IsClosed (M : Set A))).out

instance shiftMaximalIdeal_closedFact : Fact (IsClosed (shiftMaximalIdeal Γ : Set (shiftAlgebra Γ))) :=
  ⟨shiftMaximalIdeal_isClosed Γ⟩

/-- The actual complete quotient vector space from the source construction. -/
abbrev ShiftQuotient := shiftAlgebra Γ ⧸ idealSubmodule (shiftMaximalIdeal Γ)

instance shiftQuotient_nontrivial : Nontrivial (ShiftQuotient Γ) := by
  let q := (idealSubmodule (shiftMaximalIdeal Γ)).mkQ
  have hq1 : q 1 ≠ q 0 := by
    intro h
    have hmem : (1 : shiftAlgebra Γ) ∈ idealSubmodule (shiftMaximalIdeal Γ) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      simpa only [map_zero] using h
    exact shiftMaximalIdeal_ne_top Γ ((shiftMaximalIdeal Γ).eq_top hmem)
  exact ⟨⟨q 1, q 0, hq1⟩⟩

example : NormedAddCommGroup (ShiftQuotient Γ) := inferInstance
example : NormedSpace ℂ (ShiftQuotient Γ) := inferInstance
example : CompleteSpace (ShiftQuotient Γ) := inferInstance

end SurveyStatements.P2
