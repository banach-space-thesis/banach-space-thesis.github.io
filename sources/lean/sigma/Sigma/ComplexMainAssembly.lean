import Sigma.ComplexMainStatements
import Sigma.ComplexLatticeExclusion
import Sigma.ComplexConcreteAssembly
import Sigma.UniverseAssembly

/-! The complex construction yields the full nonlattice decomposition in
every universe. The obstruction is transported through an actual complex
Banach isomorphism, and the general representation theorem is applied in
the target universe; no bound on the size of possible lattice models is
assumed. -/
noncomputable section
universe u v
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

def complexContinuousLiftEquiv (K : Type v) [TopologicalSpace K] [CompactSpace K] :
    C(ULift.{u} K, ℂ) ≃L[ℂ] C(K, ℂ) := by
  let e : C(ULift.{u} K, ℂ) ≃ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun f => ⟨fun x => f (ULift.up x), f.continuous.comp continuous_uliftUp⟩
      invFun := fun f => ⟨fun x => f x.down, f.continuous.comp continuous_uliftDown⟩
      left_inv := by intro f; ext x; rfl
      right_inv := by intro f; ext x; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact LinearEquiv.toContinuousLinearEquivOfBounds e 1 1
    (by
      intro f
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x => f.norm_coe_le_norm (ULift.up x))
    (by
      intro f
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x => f.norm_coe_le_norm x.down)

theorem ComplexEnumeratedConstruction.not_complexBanachLattice_of_equiv
    (D : ComplexEnumeratedConstruction) (side : Bool)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E ≃L[ℂ] ComplexFinalCandidate D side) :
    ¬ IsomorphicToComplexBanachLattice E := by
  obtain ⟨e,he⟩ := complex_candidate_has_countable_norming
    (D.family side) (cylinderFamily (D.baseSets (!side)))
  let d : (E →L[ℂ] ℂ) ≃L[ℂ] lp (fun _ : ReducedAtom => ℂ) 1 :=
    (T.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)).trans (D.crossedDualEquiv side)
  exact complex_not_lattice_of_desiredProperty d
    ⟨complexTransportedNorming T e, complexTransportedNorming_isNorming T ⟨1,he⟩⟩
    ((complexDesiredProperty_equiv T).mpr (D.desiredProperty side))

theorem complex_theorem_1_1_completed : ComplexTheorem_1_1.{u} := by
  obtain ⟨D⟩ := complex_exists_enumeratedConstruction
  let X : ComplexBanachSpace.{u} := { Carrier := ULift.{u} (ComplexFinalCandidate D false) }
  let Y : ComplexBanachSpace.{u} := { Carrier := ULift.{u} (ComplexFinalCandidate D true) }
  let ex : X ≃L[ℂ] ComplexFinalCandidate D false := ContinuousLinearEquiv.ulift
  let ey : Y ≃L[ℂ] ComplexFinalCandidate D true := ContinuousLinearEquiv.ulift
  refine ⟨liftCompactum.{u} D.compactum,X,Y,?_,
    D.not_complexBanachLattice_of_equiv false ex,D.not_complexBanachLattice_of_equiv true ey⟩
  exact ⟨((complexContinuousLiftEquiv.{u} D.compactum).trans D.continuousCrossedEquiv).trans
    (ex.symm.prodCongr ey.symm)⟩

end SigmaNonprimarity
