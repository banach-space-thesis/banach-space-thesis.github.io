import Sigma.ConstructedDesiredProperty
import Sigma.CrossedDualEquiv
import Sigma.AtomicLatticeEmbedding
import Sigma.ConcreteAssembly
import Sigma.UniverseAssembly

/-! Assembly using the actual, already constructed crossed summands.
Only the independent ordered representation theorem remains an input.
Neither its truth nor the unconditional main theorem is asserted here. -/
noncomputable section
universe u
namespace SigmaNonprimarity
open ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

variable (hmodels : ∀ F : RealBanachLattice.{0},
  (∃ I : Type, Nonempty ((F →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)) →
  ∃ I : Type, ∃ d : (F →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1,
    ∀ φ : F →L[ℝ] ℝ, 0 ≤ φ ↔ ∀ i, 0 ≤ d φ i)

include hmodels

/-- The two actual DP obstructions exclude all Banach lattice structures as
soon as the independent ordered-dual representation theorem is available. -/
theorem EnumeratedConstruction.not_lattice_of_ordered_dual_models
    (D : EnumeratedConstruction) (side : Bool) :
    ¬ IsomorphicToBanachLattice (FinalCandidate D side) := by
  obtain ⟨e, he⟩ := candidate_has_countable_norming
    (D.family side) (cylinderFamily (D.baseSets (!side)))
  have hp := proposition_3_4_of_ordered_dual_models (FinalCandidate D side) hmodels
    ⟨e, 1, he⟩ ⟨ReducedAtom, ⟨D.crossedDualEquiv side⟩⟩
  exact fun h => D.not_sublattice side (hp.1.mp h)

/-- All concrete choices, splittings, dual models and DP conclusions are
discharged. Only the general ordered-dual-model theorem is an explicit input. -/
theorem theorem_1_1_of_ordered_dual_models : Theorem_1_1.{u} := by
  apply theorem_1_1_lift
  obtain ⟨D⟩ := exists_enumeratedConstruction
  apply theorem_1_1_of_split_families
    (D.baseSets false) (D.splitSets false) (D.baseSets true) (D.splitSets true)
    (D.splits false) (D.splits true)
    (D.family_almostDisjoint false) (D.family_almostDisjoint true)
    (D.family_infinite false) (D.family_infinite true)
  · exact D.not_lattice_of_ordered_dual_models hmodels false
  · exact D.not_lattice_of_ordered_dual_models hmodels true

theorem ckCounterexample_of_ordered_dual_models : CKCounterexample.{u} :=
  ckCounterexample_of_theorem_1_1 (theorem_1_1_of_ordered_dual_models hmodels)

theorem latticeClass_not_primary_of_ordered_dual_models :
    ¬ IsPrimaryClass (fun X : RealBanachSpace.{u} => IsomorphicToBanachLattice X) :=
  latticeClass_not_primary_of_theorem_1_1 (theorem_1_1_of_ordered_dual_models hmodels)

theorem ckClass_not_primary_of_ordered_dual_models :
    ¬ IsPrimaryClass (fun X : RealBanachSpace.{u} => IsomorphicToCK X) :=
  ckClass_not_primary_of_theorem_1_1 (theorem_1_1_of_ordered_dual_models hmodels)

end SigmaNonprimarity
