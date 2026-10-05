import Sigma.ComplexSelectedStage

/-! The actual punctured algebras supplied by the construction's four
nonseparation invariants, uniformly for either crossed summand. -/
noncomputable section
namespace SigmaNonprimarity
open Set

def ComplexEnumeratedConstruction.puncturedAlgebra (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (copy : Bool) : BooleanSubalgebra (Set ℕ) :=
  complexConstructionAlgebra D.data.choices copy (if copy = side then Set.univ \ {a} else Set.univ)

theorem ComplexEnumeratedConstruction.puncturedAlgebra_finite (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (copy : Bool) {A : Set Point} (hA : A.Finite) :
    codedSet A ∈ D.puncturedAlgebra side a copy :=
  complexConstructionAlgebra_finite_mem _ _ _ (hA.image pointCode)

theorem ComplexEnumeratedConstruction.puncturedAlgebra_family (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (copy : Bool) (i : ConstructionIndex) (bit : Bool)
    (hi : copy ≠ side ∨ i ≠ a) :
    codedSet (D.familyEquiv copy (i,bit)).val ∈ D.puncturedAlgebra side a copy := by
  have hmem : i ∈ (if copy = side then Set.univ \ {a} else Set.univ) := by
    by_cases hc : copy = side
    · simp only [if_pos hc,Set.mem_diff,Set.mem_univ,Set.mem_singleton_iff,true_and]
      exact hi.resolve_left (not_not.mpr hc)
    · simp [hc]
  have h := stageAlgebra_generator_mem
    (fun j => if copy then (D.data j).choices.2.generator else (D.data j).choices.1.generator) hmem bit
  cases copy <;> cases bit <;> exact h

theorem ComplexEnumeratedConstruction.puncturedAlgebra_univ (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (copy : Bool) : codedSet Set.univ ∈ D.puncturedAlgebra side a copy := by
  have heq : codedSet Set.univ = Set.univ := Set.image_univ_of_surjective pointCode.surjective
  rw [heq]
  exact BooleanSubalgebra.top_mem

theorem ComplexEnumeratedConstruction.choice_nonseparated (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) : (D.choice side a).PairedNonseparated (D.chargeAtSide side a)
      (D.puncturedAlgebra side a false) (D.puncturedAlgebra side a true) := by
  have h := D.good a (Set.mem_univ a)
  cases side
  · exact h.1
  · exact h.2

end SigmaNonprimarity


