import Sigma.ComplexPuncturedSeparation
import Sigma.ComplexDesiredProperty
import Sigma.ComplexModulusEmbedding

/-! Unconditional Section 6: both actual crossed spaces from the constructed
families have the desired property. Every analytic and construction hypothesis
of the three-level contradiction is supplied by a proved theorem. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem ComplexEnumeratedConstruction.desiredProperty (D : ComplexEnumeratedConstruction) (side : Bool) :
    ComplexDesiredProperty (ComplexFinalCandidate D side) := by
  intro e he
  obtain ⟨k,a,hcode⟩ := D.norming_sequence_covered side e he
  obtain ⟨c,hc⟩ := he
  let d := D.choice side a
  obtain ⟨hδ,ha,hp,hm,hz⟩ := D.selected_three_levels side a e k hcode
  refine ⟨D.distinguishedVector side a,?_⟩
  rintro ⟨g,hg⟩
  have hn := complex_no_modulus_of_three_levels (fun n => e (k n)) (fun n => hc.2.2.1 (k n))
    (D.distinguishedVector side a) (D.puncturedSpan side a) d.J₀ d.J₁ d.J₂ d.a d.delta
    hδ ha hp hm hz
    (fun g => D.distinguished_approximation side a g hδ)
    (fun s hs => D.punctured_no_gap side a e hc.2.2.1 k hcode true s hs)
    (fun s hs => D.punctured_no_gap side a e hc.2.2.1 k hcode false s hs)
  exact hn ⟨g,fun n => hg (k n)⟩

theorem complex_exists_crossed_desiredProperty : ∃ D : ComplexEnumeratedConstruction,
    ComplexDesiredProperty (ComplexFinalCandidate D false) ∧ ComplexDesiredProperty (ComplexFinalCandidate D true) := by
  obtain ⟨D⟩ := complex_exists_enumeratedConstruction
  exact ⟨D,D.desiredProperty false,D.desiredProperty true⟩

theorem ComplexEnumeratedConstruction.not_sublattice (D : ComplexEnumeratedConstruction) (side : Bool) :
    ¬ IsomorphicToComplexSublatticeEllInfinity (ComplexFinalCandidate D side) :=
  fun h => complex_not_desiredProperty_of_sublattice _ h (D.desiredProperty side)

end SigmaNonprimarity


