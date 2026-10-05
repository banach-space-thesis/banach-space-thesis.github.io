import Sigma.CylinderRepresentation
import Sigma.CompactumHeight
import Sigma.FinalFamilies

/-! The representation and exact compactum height for the actual families. -/
noncomputable section
open Set
namespace SigmaNonprimarity

private instance constructionIndexInfinite : Infinite ConstructionIndex :=
  Cardinal.infinite_iff.mpr (by
    rw [constructionIndex_cardinal]
    exact Cardinal.aleph0_le_continuum)

def EnumeratedConstruction.cylinderContinuousEquiv (D : EnumeratedConstruction) (side : Bool) :
    CylinderJL (cylinderFamily (D.baseSets side)) ≃ₗᵢ[ℝ]
      C(AUCompactum (cylinderBaseFamily (D.baseSets side)), ℝ) :=
  SigmaNonprimarity.cylinderContinuousEquiv (D.baseSets side)
    (D.baseSets_infinite side) (D.baseSets_pairwise side)

theorem EnumeratedConstruction.splitCompactum_height_three (D : EnumeratedConstruction)
    (side : Bool) :
    derivedSet (derivedSet (Set.univ : Set (AUCompactum (D.family side)))) =
        {OnePoint.infty} ∧
      derivedSet (derivedSet (derivedSet (Set.univ : Set (AUCompactum (D.family side))))) = ∅ :=
  ⟨compactum_second_derivative_eq (D.family_almostDisjoint side) (D.family_infinite side),
    compactum_third_derivative_empty (D.family_almostDisjoint side)⟩

theorem EnumeratedConstruction.cylinderCompactum_height_three (D : EnumeratedConstruction)
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
