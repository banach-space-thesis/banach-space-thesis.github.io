import Posets.FiniteIncidenceTransport
import Posets.IncidenceNorms

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜] (P : Type) [Fintype P] [PartialOrder P]

/-- The finite opposite incidence algebra, with the inherited operator norm. -/
def finiteOppositeCoordinateAlgebra : Subalgebra 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜)) :=
  (oppositeIncidenceSubalgebra 𝕜 P).map
    (operatorConjugationAlgEquiv (finiteCZeroEquiv 𝕜 P)).toAlgHom

theorem finiteOppositeCoordinateAlgebra_carrier :
    (finiteOppositeCoordinateAlgebra 𝕜 P : Set _) = oppositeFiniteIncidenceOperators 𝕜 P := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact (finite_opposite_incidence_transport S).mpr hS
  · intro hT
    let S := (finiteCZeroOperatorEquiv 𝕜 P).symm T
    refine ⟨S, ?_, ?_⟩
    · apply (finite_opposite_incidence_transport S).mp
      simpa only [S, LinearIsometryEquiv.apply_symm_apply] using hT
    · exact (finiteCZeroOperatorEquiv 𝕜 P).apply_symm_apply T

def finiteOppositeCoordinateEquiv :
    oppositeIncidenceSubalgebra 𝕜 P ≃ₗᵢ[𝕜] finiteOppositeCoordinateAlgebra 𝕜 P where
  toFun T := ⟨finiteCZeroOperatorEquiv 𝕜 P T.val, ⟨T.val, T.property, rfl⟩⟩
  invFun T := ⟨(finiteCZeroOperatorEquiv 𝕜 P).symm T.val, by
    apply (finite_opposite_incidence_transport _).mp
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (Set.ext_iff.mp (finiteOppositeCoordinateAlgebra_carrier 𝕜 P) T.val).mp T.property⟩
  left_inv T := by apply Subtype.ext; exact (finiteCZeroOperatorEquiv 𝕜 P).symm_apply_apply T.val
  right_inv T := by apply Subtype.ext; exact (finiteCZeroOperatorEquiv 𝕜 P).apply_symm_apply T.val
  map_add' S T := by apply Subtype.ext; exact map_add (finiteCZeroOperatorEquiv 𝕜 P) S.val T.val
  map_smul' a T := by apply Subtype.ext; exact map_smul (finiteCZeroOperatorEquiv 𝕜 P) a T.val
  norm_map' T := (finiteCZeroOperatorEquiv 𝕜 P).norm_map T.val

theorem finiteOppositeCoordinateEquiv_mul (S T : oppositeIncidenceSubalgebra 𝕜 P) :
    finiteOppositeCoordinateEquiv 𝕜 P (S * T) =
      finiteOppositeCoordinateEquiv 𝕜 P S * finiteOppositeCoordinateEquiv 𝕜 P T := by
  apply Subtype.ext
  exact finiteCZeroOperatorEquiv_mul S.val T.val

end Posets
