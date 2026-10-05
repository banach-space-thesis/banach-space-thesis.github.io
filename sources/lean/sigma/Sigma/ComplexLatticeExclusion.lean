import Sigma.ComplexLatticeRepresentation
import Sigma.ComplexConstructedDesiredProperty
import Sigma.ComplexCrossedDualEquiv
import Sigma.ComplexCountableNorming

/-! Each actual crossed summand is excluded from the full class of complex
Banach lattices by the proved ordered-dual representation implication. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem ComplexEnumeratedConstruction.not_complexBanachLattice
    (D : ComplexEnumeratedConstruction) (side : Bool) :
    ¬ IsomorphicToComplexBanachLattice (ComplexFinalCandidate D side) := by
  obtain ⟨e,he⟩ := complex_candidate_has_countable_norming
    (D.family side) (cylinderFamily (D.baseSets (!side)))
  exact complex_not_lattice_of_desiredProperty (D.crossedDualEquiv side)
    ⟨e,1,he⟩ (D.desiredProperty side)

theorem complex_exists_crossed_not_lattice :
    ∃ D : ComplexEnumeratedConstruction,
      ¬ IsomorphicToComplexBanachLattice (ComplexFinalCandidate D false) ∧
      ¬ IsomorphicToComplexBanachLattice (ComplexFinalCandidate D true) := by
  obtain ⟨D⟩ := complex_exists_enumeratedConstruction
  exact ⟨D,D.not_complexBanachLattice false,D.not_complexBanachLattice true⟩

end SigmaNonprimarity

