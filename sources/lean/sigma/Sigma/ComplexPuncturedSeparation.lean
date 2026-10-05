import Sigma.ComplexPuncturedGenerators
import Sigma.ComplexPuncturedAlgebras
import Sigma.ComplexSelectedCoordinateCharge
import Sigma.ComplexSpanSeparation

/-! Transfer the construction's nonseparation to the span of actual projected
generators in the crossed Banach space. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem complexFinitelySeparated_of_test_representatives {D I J : Type*} [Nonempty J]
    (ev : D → I → ℂ) (ev' : D → J → ℂ) (S : Set I) (T : Set J) (M N : Set D)
    (hrep : ∀ i ∈ S, ∃ j ∈ T, ∀ d, ev d i = ev' d j)
    (h : ComplexFinitelySeparated ev S M N) : ComplexFinitelySeparated ev' T M N := by
  classical
  let r : I → J := fun i => if hi : i ∈ S then Classical.choose (hrep i hi) else Classical.arbitrary J
  have hr (i : I) (hi : i ∈ S) : r i ∈ T ∧ ∀ d, ev d i = ev' d (r i) := by
    simpa only [r,dif_pos hi] using Classical.choose_spec (hrep i hi)
  obtain ⟨ε,hε,F,hF,hsep⟩ := h
  refine ⟨ε,hε,F.image r,?_,?_⟩
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact (hr i (hF hi)).1
  · intro m hm n hn
    obtain ⟨i,hi,he⟩ := hsep m hm n hn
    refine ⟨r i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    simpa only [(hr i (hF hi)).2 m,(hr i (hF hi)).2 n] using he


abbrev ComplexPuncturedTests (D : ComplexEnumeratedConstruction) (side : Bool) (a : ConstructionIndex) :=
  D.puncturedAlgebra side a false ⊕ D.puncturedAlgebra side a true

def ComplexEnumeratedConstruction.testInCopy (D : ComplexEnumeratedConstruction) (side : Bool) (a : ConstructionIndex)
    (copy : Bool) (A : Set Point) (hA : codedSet A ∈ D.puncturedAlgebra side a copy) :
    ComplexPuncturedTests D side a := by
  cases copy
  · exact .inl ⟨codedSet A,hA⟩
  · exact .inr ⟨codedSet A,hA⟩

theorem ComplexEnumeratedConstruction.pairedTest_testInCopy (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (copy : Bool) (A : Set Point)
    (hA : codedSet A ∈ D.puncturedAlgebra side a copy) :
    pairedTest (D.puncturedAlgebra side a false) (D.puncturedAlgebra side a true)
      (D.testInCopy side a copy A hA) = oneCopySet copy A := by
  cases copy <;> rfl

theorem ComplexEnumeratedConstruction.punctured_generator_rep (D : ComplexEnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ)
    (he : ∀ n, ‖e n‖ ≤ 1) (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (f : ComplexFinalCandidate D side) (hf : f ∈ D.puncturedGenerators side a) :
    ∃ t : ComplexPuncturedTests D side a, ∀ n, e (k n) f = D.chargeAtSide side a n
      (pairedTest (D.puncturedAlgebra side a false) (D.puncturedAlgebra side a true) t) := by
  rcases hf with ((⟨copy,p,rfl⟩ | ⟨copy,i,bit,hi,rfl⟩) | ⟨copy,rfl⟩)
  · refine ⟨D.testInCopy side a copy {p} (D.puncturedAlgebra_finite side a copy (Set.finite_singleton p)),?_⟩
    intro n
    rw [D.pairedTest_testInCopy]
    exact (D.selected_coordinate_charge side a e he k hcode copy
      (BooleanSubalgebra.subset_closure (Or.inr (Set.finite_singleton p)))
      (complexCharacteristic_singleton_mem_ComplexJL _ p) n).symm
  · refine ⟨D.testInCopy side a copy (D.familyEquiv copy (i,bit)).val
      (D.puncturedAlgebra_family side a copy i bit hi),?_⟩
    intro n
    rw [D.pairedTest_testInCopy]
    exact (D.selected_coordinate_charge side a e he k hcode copy
      (BooleanSubalgebra.subset_closure (Or.inl (D.familyEquiv copy (i,bit)).property))
      (complexCharacteristic_mem_ComplexJL (D.familyEquiv copy (i,bit)).property) n).symm
  · refine ⟨D.testInCopy side a copy Set.univ (D.puncturedAlgebra_univ side a copy),?_⟩
    intro n
    rw [D.pairedTest_testInCopy]
    exact (D.selected_coordinate_charge side a e he k hcode copy
      BooleanSubalgebra.top_mem (complexConstant_mem_ComplexJL _) n).symm

theorem ComplexEnumeratedConstruction.punctured_nonseparation (D : ComplexEnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ)
    (he : ∀ n, ‖e n‖ ≤ 1) (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (cut : Bool) :
    ¬ ComplexFinitelySeparated (fun n f => e (k n) f) (D.puncturedGenerators side a)
      ((D.choice side a).cutLeft cut) ((D.choice side a).cutRight cut) := by
  intro hsep
  let ev : ℕ → ComplexPuncturedTests D side a → ℂ := fun n t =>
    D.chargeAtSide side a n (pairedTest (D.puncturedAlgebra side a false) (D.puncturedAlgebra side a true) t)
  have hrep : ∀ f ∈ D.puncturedGenerators side a, ∃ t ∈ (Set.univ : Set (ComplexPuncturedTests D side a)),
      ∀ n, e (k n) f = ev n t := by
    intro f hf
    obtain ⟨t,ht⟩ := D.punctured_generator_rep side a e he k hcode f hf
    exact ⟨t,Set.mem_univ _,ht⟩
  have ht := complexFinitelySeparated_of_test_representatives (fun n f => e (k n) f) ev
    (D.puncturedGenerators side a) Set.univ _ _ hrep hsep
  have hn := (ComplexThreeLevelChoice.pairedNonseparated_iff_cuts _ _ _ _).mp (D.choice_nonseparated side a) cut
  apply hn
  exact (complexFinitelySeparated_image_iff _ (D.chargeAtSide side a) Set.univ _ _).mpr ht

theorem ComplexEnumeratedConstruction.punctured_no_gap (D : ComplexEnumeratedConstruction)
    (side : Bool) (a : ConstructionIndex) (e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ)
    (he : ∀ n, ‖e n‖ ≤ 1) (k : ℕ → ℕ)
    (hcode : D.codeAtSide side a = fun n => D.coefficients (D.extendCrossedFunctional side (e (k n))))
    (cut : Bool) (s : ComplexFinalCandidate D side) (hs : s ∈ D.puncturedSpan side a) :
    ¬ ComplexUniformGap (fun n => e (k n) s) ((D.choice side a).cutLeft cut) ((D.choice side a).cutRight cut) :=
  complex_no_gap_on_span (fun n => e (k n)) (D.puncturedGenerators side a) _ _
    (D.punctured_nonseparation side a e he k hcode cut) s hs

end SigmaNonprimarity


