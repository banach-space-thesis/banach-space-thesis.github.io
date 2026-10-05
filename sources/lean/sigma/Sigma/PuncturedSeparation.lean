import Sigma.PuncturedGenerators
import Sigma.PuncturedAlgebras
import Sigma.CoordinateCharge
import Sigma.Separation
import ThesisCommon.Analysis.SeparationTests

/-! Transfer the construction's nonseparation to the span of actual projected
generators in the crossed Banach space. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

abbrev PuncturedTests (D : EnumeratedConstruction) (side : Bool) (a : ConstructionIndex) :=
  D.puncturedAlgebra side a false ⊕ D.puncturedAlgebra side a true

def EnumeratedConstruction.testInCopy (D : EnumeratedConstruction) (side : Bool) (a : ConstructionIndex)
    (copy : Bool) (A : Set Point) (hA : codedSet A ∈ D.puncturedAlgebra side a copy) :
    PuncturedTests D side a := by
  cases copy
  · exact .inl ⟨codedSet A,hA⟩
  · exact .inr ⟨codedSet A,hA⟩

theorem EnumeratedConstruction.pairedTest_testInCopy (D : EnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (copy : Bool) (A : Set Point)
    (hA : codedSet A ∈ D.puncturedAlgebra side a copy) :
    pairedTest (D.puncturedAlgebra side a false) (D.puncturedAlgebra side a true)
      (D.testInCopy side a copy A hA) = oneCopySet copy A := by
  cases copy <;> rfl

theorem EnumeratedConstruction.punctured_generator_rep (D : EnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → FinalCandidate D side →L[ℝ] ℝ)
    (he : ∀ n, ‖e n‖ ≤ 1) (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (f : FinalCandidate D side) (hf : f ∈ D.puncturedGenerators side a) :
    ∃ t : PuncturedTests D side a, ∀ n, e (k n) f = D.chargeAtSide side a n
      (pairedTest (D.puncturedAlgebra side a false) (D.puncturedAlgebra side a true) t) := by
  rcases hf with ((⟨copy,p,rfl⟩ | ⟨copy,i,bit,hi,rfl⟩) | ⟨copy,rfl⟩)
  · refine ⟨D.testInCopy side a copy {p} (D.puncturedAlgebra_finite side a copy (Set.finite_singleton p)),?_⟩
    intro n
    rw [D.pairedTest_testInCopy]
    exact (D.selected_coordinate_charge side a e he k hcode copy
      (BooleanSubalgebra.subset_closure (Or.inr (Set.finite_singleton p)))
      (characteristic_singleton_mem_JL _ p) n).symm
  · refine ⟨D.testInCopy side a copy (D.familyEquiv copy (i,bit)).val
      (D.puncturedAlgebra_family side a copy i bit hi),?_⟩
    intro n
    rw [D.pairedTest_testInCopy]
    exact (D.selected_coordinate_charge side a e he k hcode copy
      (BooleanSubalgebra.subset_closure (Or.inl (D.familyEquiv copy (i,bit)).property))
      (characteristic_mem_JL (D.familyEquiv copy (i,bit)).property) n).symm
  · refine ⟨D.testInCopy side a copy Set.univ (D.puncturedAlgebra_univ side a copy),?_⟩
    intro n
    rw [D.pairedTest_testInCopy]
    exact (D.selected_coordinate_charge side a e he k hcode copy
      BooleanSubalgebra.top_mem (constant_mem_JL _) n).symm

theorem EnumeratedConstruction.punctured_nonseparation (D : EnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → FinalCandidate D side →L[ℝ] ℝ)
    (he : ∀ n, ‖e n‖ ≤ 1) (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (cut : Bool) :
    ¬ FinitelySeparated (fun n f => e (k n) f) (D.puncturedGenerators side a)
      ((D.choice side a).cutLeft cut) ((D.choice side a).cutRight cut) := by
  intro hsep
  let ev : ℕ → PuncturedTests D side a → ℝ := fun n t =>
    D.chargeAtSide side a n (pairedTest (D.puncturedAlgebra side a false) (D.puncturedAlgebra side a true) t)
  have hrep : ∀ f ∈ D.puncturedGenerators side a, ∃ t ∈ (Set.univ : Set (PuncturedTests D side a)),
      ∀ n, e (k n) f = ev n t := by
    intro f hf
    obtain ⟨t,ht⟩ := D.punctured_generator_rep side a e he k hcode f hf
    exact ⟨t,Set.mem_univ _,ht⟩
  have ht := finitelySeparated_of_test_representatives (fun n f => e (k n) f) ev
    (D.puncturedGenerators side a) Set.univ _ _ hrep hsep
  have hn := (ThreeLevelChoice.nonseparated_iff_cuts _ _ _ _).mp (D.choice_nonseparated side a) cut
  apply hn
  exact (finitelySeparated_image_iff _ (D.chargeAtSide side a) Set.univ _ _).mpr ht

theorem EnumeratedConstruction.punctured_no_gap (D : EnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → FinalCandidate D side →L[ℝ] ℝ)
    (he : ∀ n, ‖e n‖ ≤ 1) (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (cut : Bool) (s : FinalCandidate D side) (hs : s ∈ D.puncturedSpan side a) :
    ¬ UniformGap (fun n => e (k n) s) ((D.choice side a).cutLeft cut) ((D.choice side a).cutRight cut) :=
  no_gap_on_span (fun n => e (k n)) (D.puncturedGenerators side a) _ _
    (D.punctured_nonseparation side a e he k hcode cut) s hs

end SigmaNonprimarity
