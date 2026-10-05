import Sigma.ComplexConstructedDesiredProperty
import Sigma.ComplexConcreteAssembly
import Sigma.ComplexCrossedDualEquiv
import Sigma.ComplexCountableNorming

/-! Unconditional complex concrete endpoint. The abstract implication from
an arbitrary complex Banach-lattice representative to a modulus-closed
ℓ∞ model is a separate theorem and is not claimed here. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem complex_exists_ck_decomposition_without_modulus_embedding :
    ∃ D : ComplexEnumeratedConstruction,
      Nonempty (C(D.compactum,ℂ) ≃L[ℂ]
        (ComplexFinalCandidate D false × ComplexFinalCandidate D true)) ∧
      (∀ side : Bool, ¬ IsomorphicToComplexSublatticeEllInfinity (ComplexFinalCandidate D side)) ∧
      (∀ side : Bool, Nonempty ((ComplexFinalCandidate D side →L[ℂ] ℂ) ≃L[ℂ]
        lp (fun _ : ReducedAtom => ℂ) 1)) ∧
      (∀ side : Bool, ∃ e : ℕ → ComplexFinalCandidate D side →L[ℂ] ℂ,
        IsComplexCNorming e 1) := by
  obtain ⟨D⟩ := complex_exists_enumeratedConstruction
  exact ⟨D,D.continuousCrossedEquiv_nonempty,D.not_sublattice,
    fun side => ⟨D.crossedDualEquiv side⟩,
    fun side => complex_candidate_has_countable_norming _ _⟩

end SigmaNonprimarity

