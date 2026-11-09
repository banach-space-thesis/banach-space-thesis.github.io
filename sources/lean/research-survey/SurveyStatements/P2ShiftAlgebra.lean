import SurveyStatements.P2Shifts
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Analysis.Normed.Algebra.Basic

/-! The closed unital shift algebra used before taking the maximal-ideal quotient. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace SurveyStatements.P2
universe u
variable (Γ : Type u)
local instance : DecidableEq Γ := Classical.decEq Γ

/-- Prefix and removal generators. -/
def shiftGenerators : Set (BoundedOperators (WordC0 Γ)) :=
  Set.range (prefixOperator (Γ := Γ)) ∪ Set.range (removalOperator (Γ := Γ))

/-- The source's norm-closed unital complex algebra of word shifts. -/
def shiftAlgebra : Subalgebra ℂ (BoundedOperators (WordC0 Γ)) :=
  (Algebra.adjoin ℂ (shiftGenerators Γ)).topologicalClosure

theorem shiftAlgebra_isClosed : IsClosed (shiftAlgebra Γ : Set (BoundedOperators (WordC0 Γ))) :=
  Subalgebra.isClosed_topologicalClosure _

instance shiftAlgebra_completeSpace : CompleteSpace (shiftAlgebra Γ) :=
  (shiftAlgebra_isClosed Γ).completeSpace_coe

instance shiftAlgebra_nontrivial : Nontrivial (shiftAlgebra Γ) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have heval := congrArg (fun T : shiftAlgebra Γ => (T : BoundedOperators (WordC0 Γ))
    (wordUnit ([] : List Γ)) []) h
  simpa [wordUnit] using heval

/-- The closed shift algebra is a genuine nonzero unital complex Banach algebra. -/
def shiftBanachAlgebra : ComplexBanachAlgebra where
  Carrier := shiftAlgebra Γ

theorem prefixOperator_mem_shiftAlgebra (a : Γ) : prefixOperator a ∈ shiftAlgebra Γ := by
  apply (Algebra.adjoin ℂ (shiftGenerators Γ)).le_topologicalClosure
  apply Algebra.subset_adjoin
  exact Or.inl ⟨a, rfl⟩

theorem removalOperator_mem_shiftAlgebra (a : Γ) : removalOperator a ∈ shiftAlgebra Γ := by
  apply (Algebra.adjoin ℂ (shiftGenerators Γ)).le_topologicalClosure
  apply Algebra.subset_adjoin
  exact Or.inr ⟨a, rfl⟩

/-- The prefix generator as an element of the closed algebra. -/
def algebraPrefix (a : Γ) : shiftAlgebra Γ :=
  ⟨prefixOperator a, prefixOperator_mem_shiftAlgebra Γ a⟩

/-- The removal generator as an element of the closed algebra. -/
def algebraRemoval (a : Γ) : shiftAlgebra Γ :=
  ⟨removalOperator a, removalOperator_mem_shiftAlgebra Γ a⟩

@[simp] theorem norm_algebraPrefix (a : Γ) : ‖algebraPrefix Γ a‖ = 1 :=
  norm_prefixOperator a

@[simp] theorem norm_algebraRemoval (a : Γ) : ‖algebraRemoval Γ a‖ = 1 :=
  norm_removalOperator a

/-- The exact shift relation also holds inside the concrete closed algebra. -/
theorem algebraRemoval_mul_algebraPrefix (a b : Γ) :
    algebraRemoval Γ a * algebraPrefix Γ b = if a = b then 1 else 0 := by
  classical
  apply Subtype.ext
  by_cases h : a = b <;>
    simpa [algebraRemoval, algebraPrefix, h] using
      removalOperator_mul_prefixOperator a b

theorem norm_sum_algebraPrefix_le (F : Finset Γ) (a : Γ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ b ∈ F, ‖a b‖ ≤ C) :
    ‖∑ b ∈ F, a b • algebraPrefix Γ b‖ ≤ C := by
  change ‖(↑(∑ b ∈ F, a b • algebraPrefix Γ b : shiftAlgebra Γ) :
    BoundedOperators (WordC0 Γ))‖ ≤ C
  change ‖(shiftAlgebra Γ).val (∑ b ∈ F, a b • algebraPrefix Γ b)‖ ≤ C
  rw [map_sum]
  simpa only [map_smul, algebraPrefix, Subalgebra.val_apply, Subtype.coe_mk] using
    norm_sum_prefixOperators_le F a C hC ha

end SurveyStatements.P2
