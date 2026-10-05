import Posets.TriangularIncidenceQuotient

/-! Completeness and admissibility of the concrete bipartite algebra. -/
noncomputable section
open ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜] (P Q : Type*)
local instance realizationCompleteBipartiteOrder : PartialOrder (P ⊕ Q) := completeBipartiteOrder

instance bipartite_completeSpace : CompleteSpace (BipartiteAlgebra 𝕜 P Q) :=
  (incidenceOperators_isClosed (𝕜 := 𝕜) (P := P ⊕ Q)).completeSpace_coe

def bipartiteInclusion : BoundedHom 𝕜 (BipartiteAlgebra 𝕜 P Q)
    (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q)) where
  toContinuousLinearMap := (BipartiteAlgebra 𝕜 P Q).toSubmodule.subtypeL
  map_mul' := fun _ _ => rfl

theorem bipartiteInclusion_isometry : Isometry (bipartiteInclusion 𝕜 P Q) :=
  isometry_subtype_coe

theorem bipartiteInclusion_range :
    Set.range (bipartiteInclusion 𝕜 P Q) = incidenceOperators 𝕜 (P ⊕ Q) := by
  exact Subtype.range_coe

theorem bipartite_admissible (P Q : Type) [Countable P] [Countable Q] :
    AdmissibleAlgebra 𝕜 (BipartiteAlgebra 𝕜 P Q) := by
  refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
  exact ⟨P ⊕ Q, inferInstance, completeBipartiteOrder,
    bipartiteInclusion 𝕜 P Q, bipartiteInclusion_isometry 𝕜 P Q,
    bipartiteInclusion_range 𝕜 P Q⟩

end Posets
