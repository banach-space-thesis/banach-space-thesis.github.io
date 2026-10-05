import Posets.FiniteIncidenceRepresentation

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P]
  [LocallyFiniteOrder P] [Fintype P]

omit [LocallyFiniteOrder P] in
theorem finiteIncidenceOperator_one :
    finiteIncidenceOperator (1 : IncidenceAlgebra 𝕜 P) = 1 := by
  ext x s
  simp [finiteIncidenceOperator_apply, IncidenceAlgebra.one_apply]

def finiteIncidenceAlgHom : IncidenceAlgebra 𝕜 P →ₐ[𝕜] ((P → 𝕜) →L[𝕜] (P → 𝕜)) where
  toFun := finiteIncidenceOperator
  map_zero' := finiteIncidenceOperator_zero
  map_one' := finiteIncidenceOperator_one
  map_add' := finiteIncidenceOperator_add
  map_mul' := finiteIncidenceOperator_mul
  commutes' := by
    intro a
    rw [Algebra.algebraMap_eq_smul_one, finiteIncidenceOperator_smul,
      finiteIncidenceOperator_one, Algebra.algebraMap_eq_smul_one]

def finiteIncidenceSubalgebra : Subalgebra 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜)) :=
  (finiteIncidenceAlgHom (𝕜 := 𝕜) (P := P)).range

def finiteOperatorMatrix (T : (P → 𝕜) →L[𝕜] (P → 𝕜))
    (hT : T ∈ finiteIncidenceOperators 𝕜 P) : IncidenceAlgebra 𝕜 P where
  toFun s t := T (Pi.single t 1) s
  eq_zero_of_not_le' := fun s t hst => hT s t hst

omit [LocallyFiniteOrder P] [PartialOrder P] in
theorem finiteCoordinateExpansion (x : P → 𝕜) :
    x = ∑ t : P, x t • (Pi.single t (1 : 𝕜) : P → 𝕜) := by
  funext s
  simp [Pi.single_apply]

omit [LocallyFiniteOrder P] in
theorem finiteOperatorMatrix_inverse (T : (P → 𝕜) →L[𝕜] (P → 𝕜))
    (hT : T ∈ finiteIncidenceOperators 𝕜 P) :
    finiteIncidenceOperator (finiteOperatorMatrix T hT) = T := by
  ext x s
  change (∑ t : P, T (Pi.single t 1) s * x t) = T x s
  conv_rhs => rw [finiteCoordinateExpansion x]
  simp [map_sum, map_smul, Finset.sum_apply, mul_comm]

theorem finiteIncidenceSubalgebra_carrier :
    (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P) : Set _) = finiteIncidenceOperators 𝕜 P := by
  ext T
  constructor
  · rintro ⟨f, rfl⟩ s t hst
    change finiteIncidenceOperator f (Pi.single t 1) s = 0
    rw [finiteIncidenceOperator_single]
    exact IncidenceAlgebra.apply_eq_zero_of_not_le hst f
  · intro hT
    exact ⟨finiteOperatorMatrix T hT, finiteOperatorMatrix_inverse T hT⟩

/-- Exact algebra identification with the finite zero-pattern operator algebra.
The codomain carries the inherited operator norm used by the paper. -/
def finiteIncidenceAlgebraEquiv : IncidenceAlgebra 𝕜 P ≃ₐ[𝕜]
    finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P) :=
  AlgEquiv.ofInjective finiteIncidenceAlgHom finiteIncidenceOperator_injective

def oppositeFiniteIncidenceSubalgebra : Subalgebra 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜)) :=
  finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := Pᵒᵈ)

theorem oppositeFiniteIncidenceSubalgebra_carrier :
    (oppositeFiniteIncidenceSubalgebra (𝕜 := 𝕜) (P := P) : Set _) =
      oppositeFiniteIncidenceOperators 𝕜 P :=
  finiteIncidenceSubalgebra_carrier (𝕜 := 𝕜) (P := Pᵒᵈ)

theorem finiteIncidenceOperators_isClosed : IsClosed (finiteIncidenceOperators 𝕜 P) := by
  rw [← finiteIncidenceSubalgebra_carrier]
  exact (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)).toSubmodule.closed_of_finiteDimensional

end Posets
