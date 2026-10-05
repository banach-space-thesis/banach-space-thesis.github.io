import Posets.FiniteCZeroEquiv
import PosetsCommon.OperatorConjugation

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [Fintype P]

def finiteCZeroOperatorEquiv (𝕜 : Type) [RCLike 𝕜] (P : Type) [Fintype P] :
    (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) ≃ₗᵢ[𝕜] ((P → 𝕜) →L[𝕜] (P → 𝕜)) :=
  operatorConjugationIsometry (finiteCZeroEquiv 𝕜 P)

theorem finiteCZeroOperatorEquiv_matrix (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) (s t : P) :
    finiteCZeroOperatorEquiv 𝕜 P T (Pi.single t 1) s = scalarMatrix 𝕜 T s t := by
  change (finiteCZeroEquiv 𝕜 P)
    (T ((finiteCZeroEquiv 𝕜 P).symm (Pi.single t 1))) s = _
  rw [← finiteCZeroEquiv_unitVector 𝕜 P t, LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem finiteCZeroOperatorEquiv_mul (S T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :
    finiteCZeroOperatorEquiv 𝕜 P (S * T) = finiteCZeroOperatorEquiv 𝕜 P S * finiteCZeroOperatorEquiv 𝕜 P T :=
  operatorConjugation_mul (finiteCZeroEquiv 𝕜 P) S T

theorem finite_incidence_transport [PartialOrder P] (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :
    finiteCZeroOperatorEquiv 𝕜 P T ∈ finiteIncidenceOperators 𝕜 P ↔ T ∈ incidenceOperators 𝕜 P := by
  simp only [finiteIncidenceOperators, incidenceOperators, Set.mem_setOf_eq,
    finiteCZeroOperatorEquiv_matrix]

theorem finite_opposite_incidence_transport [PartialOrder P] (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :
    finiteCZeroOperatorEquiv 𝕜 P T ∈ oppositeFiniteIncidenceOperators 𝕜 P ↔
      T ∈ oppositeIncidenceOperators 𝕜 P := by
  simp only [oppositeFiniteIncidenceOperators, oppositeIncidenceOperators, Set.mem_setOf_eq,
    finiteCZeroOperatorEquiv_matrix]

end Posets
