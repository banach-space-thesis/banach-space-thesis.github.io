import Sigma.PuncturedSeparation
import Sigma.DesiredProperty
import Sigma.ModulusEmbedding

/-! Unconditional Section 6: both actual crossed spaces from the constructed
families have the desired property. Every analytic and construction hypothesis
of the three-level contradiction is supplied by a proved theorem. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

theorem EnumeratedConstruction.desiredProperty (D : EnumeratedConstruction) (side : Bool) :
    DesiredProperty (FinalCandidate D side) := by
  intro e he
  obtain ⟨k,a,hcode⟩ := D.norming_sequence_covered side e he
  obtain ⟨c,hc⟩ := he
  let d := D.choice side a
  obtain ⟨hδ,ha,hp,hm,hz⟩ := D.selected_three_levels side a e k hcode
  refine ⟨D.distinguishedVector side a,?_⟩
  rintro ⟨g,hg⟩
  have hn := no_modulus_of_three_levels (fun n => e (k n)) (fun n => hc.2.2.1 (k n))
    (D.distinguishedVector side a) (D.puncturedSpan side a) d.J₀ d.J₁ d.J₂ d.a d.delta
    hδ ha hp hm hz
    (fun g => D.distinguished_approximation side a g hδ)
    (fun s hs => D.punctured_no_gap side a e hc.2.2.1 k hcode true s hs)
    (fun s hs => D.punctured_no_gap side a e hc.2.2.1 k hcode false s hs)
  exact hn ⟨g,fun n => hg (k n)⟩

theorem exists_crossed_desiredProperty : ∃ D : EnumeratedConstruction,
    DesiredProperty (FinalCandidate D false) ∧ DesiredProperty (FinalCandidate D true) := by
  obtain ⟨D⟩ := exists_enumeratedConstruction
  exact ⟨D,D.desiredProperty false,D.desiredProperty true⟩

theorem EnumeratedConstruction.not_sublattice (D : EnumeratedConstruction) (side : Bool) :
    ¬ IsomorphicToSublatticeEllInfinity (FinalCandidate D side) :=
  fun h => not_desiredProperty_of_sublattice _ h (D.desiredProperty side)

end SigmaNonprimarity
