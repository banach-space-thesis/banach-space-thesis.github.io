import Sigma.ComplexCrossedProjection
import Sigma.ComplexCylinderRepresentation
import Sigma.ConcreteAssembly
import Sigma.CompactumHeight
import ThesisCommon.Analysis.SigmaComplexFiniteSums

/-! The concrete C(K,ℂ) decomposition for the actual two complex families. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

private instance complexConstructionIndexInfinite : Infinite ConstructionIndex :=
  Cardinal.infinite_iff.mpr (by
    rw [constructionIndex_cardinal]
    exact Cardinal.aleph0_le_continuum)

/-- The complex version of Equation (3), using the actual closed spans. -/
def complexContinuousSplitEquiv {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point)
    (hsplit : ∀ i, Splits (J i) (b i)) (hB : AlmostDisjoint (splitFamily J b))
    (hInf : (splitFamily J b).Infinite) :
    C(AUCompactum (splitFamily J b), ℂ) ≃L[ℂ]
      ComplexCylinderJL (cylinderFamily J) × complexAntisymmetricJL (splitFamily J b) :=
  (complexJLContinuousEquiv hB hInf).symm.toContinuousLinearEquiv.trans
    (complexSplitJLEquiv J b hsplit)

/-- The disjoint union of the actual two Mrówka compactifications. -/
def ComplexEnumeratedConstruction.compactum (D : ComplexEnumeratedConstruction) : Compactum :=
  { Carrier := AUCompactum (D.family false) ⊕ AUCompactum (D.family true)
    t2Space := by
      letI := mrowkaT2 (D.family_almostDisjoint false)
      letI := mrowkaT2 (D.family_almostDisjoint true)
      infer_instance }

/-- C(K,ℂ) is the product of the two concrete crossed summands. -/
def ComplexEnumeratedConstruction.continuousCrossedEquiv (D : ComplexEnumeratedConstruction) :
    C(AUCompactum (D.family false) ⊕ AUCompactum (D.family true),ℂ) ≃L[ℂ]
      (ComplexFinalCandidate D false × ComplexFinalCandidate D true) :=
  (complexContinuousSumEquiv _ _).trans
    (((complexContinuousSplitEquiv (D.baseSets false) (D.splitSets false) (D.splits false)
      (D.family_almostDisjoint false) (D.family_infinite false)).prodCongr
      (complexContinuousSplitEquiv (D.baseSets true) (D.splitSets true) (D.splits true)
        (D.family_almostDisjoint true) (D.family_infinite true))).trans
      (complexCrossRegroup _ _ _ _))

theorem ComplexEnumeratedConstruction.continuousCrossedEquiv_nonempty (D : ComplexEnumeratedConstruction) :
    Nonempty (C(D.compactum,ℂ) ≃L[ℂ]
      (ComplexFinalCandidate D false × ComplexFinalCandidate D true)) :=
  ⟨D.continuousCrossedEquiv⟩

/-- The compactum associated with the cylinder component on either side. -/
def ComplexEnumeratedConstruction.cylinderCompactum (D : ComplexEnumeratedConstruction)
    (side : Bool) : Compactum :=
  auCompactumBundle (cylinderBaseFamily_almostDisjoint (D.baseSets side)
    (D.baseSets_infinite side) (D.baseSets_pairwise side))

/-- Each cylinder component is an actual complex C(K) space, isometrically. -/
def ComplexEnumeratedConstruction.cylinderContinuousEquiv (D : ComplexEnumeratedConstruction)
    (side : Bool) : ComplexCylinderJL (cylinderFamily (D.baseSets side)) ≃ₗᵢ[ℂ]
      C(D.cylinderCompactum side,ℂ) :=
  complexCylinderContinuousEquiv (D.baseSets side) (D.baseSets_infinite side)
    (D.baseSets_pairwise side)

theorem ComplexEnumeratedConstruction.splitCompactum_height_three (D : ComplexEnumeratedConstruction)
    (side : Bool) :
    derivedSet (derivedSet (Set.univ : Set (AUCompactum (D.family side)))) =
        {OnePoint.infty} ∧
      derivedSet (derivedSet (derivedSet (Set.univ : Set (AUCompactum (D.family side))))) = ∅ :=
  ⟨compactum_second_derivative_eq (D.family_almostDisjoint side) (D.family_infinite side),
    compactum_third_derivative_empty (D.family_almostDisjoint side)⟩

theorem ComplexEnumeratedConstruction.cylinderCompactum_height_three (D : ComplexEnumeratedConstruction)
    (side : Bool) :
    derivedSet (derivedSet
      (Set.univ : Set (AUCompactum (cylinderBaseFamily (D.baseSets side))))) =
        {OnePoint.infty} ∧
      derivedSet (derivedSet (derivedSet
        (Set.univ : Set (AUCompactum (cylinderBaseFamily (D.baseSets side)))))) = ∅ := by
  have hAD := cylinderBaseFamily_almostDisjoint (D.baseSets side)
    (D.baseSets_infinite side) (D.baseSets_pairwise side)
  have hInf := cylinderBaseFamily_infinite (D.baseSets side)
    (D.baseSets_infinite side) (D.baseSets_pairwise side)
  exact ⟨compactum_second_derivative_eq hAD hInf, compactum_third_derivative_empty hAD⟩

end SigmaNonprimarity

