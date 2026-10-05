import Posets.CommonQuotientSection
import Posets.FiniteIncidenceQuotientCoordinates
import Posets.StrongSplitTransport
import PosetsCommon.CZeroSumFiniteEquiv

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [Fintype P]

theorem finite_zeroColumns (M : P → P → 𝕜) : ZeroColumnsOn 𝕜 M := by
  simp [ZeroColumnsOn, Filter.cofinite_eq_bot]

variable [PartialOrder P] [Nonempty P]
  {X : P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, CompleteSpace (X p)] {ι : ∀ s t, X s →L[𝕜] X t}
  (h : FewOperators 𝕜 X ι) (hcommon : CommonSubspace 𝕜 X ι)

/-- The finite scalar-coefficient quotient on the paper's supremum-norm sum. -/
def finiteScalarQuotientHom :
    BoundedHom 𝕜 ((∀ p, X p) →L[𝕜] (∀ p, X p)) (finiteOppositeCoordinateAlgebra 𝕜 P) :=
  transportQuotient (finiteCZeroSumEquiv X) (finiteOppositeCoordinateEquiv 𝕜 P)
    (finiteOppositeCoordinateEquiv_mul 𝕜 P)
    (commonScalarQuotientHom h hcommon (fun T => finite_zeroColumns (blockScalarMatrix h T)))

/-- Lift a finite scalar matrix to the prescribed connecting-operator matrix. -/
def finiteIncidenceLiftHom :
    BoundedHom 𝕜 (finiteOppositeCoordinateAlgebra 𝕜 P) ((∀ p, X p) →L[𝕜] (∀ p, X p)) :=
  transportSection (finiteCZeroSumEquiv X) (finiteOppositeCoordinateEquiv 𝕜 P)
    (finiteOppositeCoordinateEquiv_mul 𝕜 P) (incidenceLiftHom h)

theorem finiteScalarQuotientHom_matrix (T : (∀ p, X p) →L[𝕜] (∀ p, X p)) (s t : P) :
    (finiteScalarQuotientHom h hcommon T).val (Pi.single t 1) s =
      blockScalarMatrix h (operatorConjugation (finiteCZeroSumEquiv X).symm T) s t := by
  change finiteCZeroOperatorEquiv 𝕜 P
    (commonScalarQuotientValue h hcommon
      (fun U => finite_zeroColumns (blockScalarMatrix h U))
      (operatorConjugation (finiteCZeroSumEquiv X).symm T)).val (Pi.single t 1) s = _
  rw [finiteCZeroOperatorEquiv_matrix, scalarMatrix_commonScalarQuotientValue]

theorem finiteIncidenceLiftHom_block (T : finiteOppositeCoordinateAlgebra 𝕜 P)
    (s t : P) (x : X t) :
    finiteIncidenceLiftHom h T (Pi.single t x) s = T.val (Pi.single t 1) s • ι t s x := by
  let U := (finiteOppositeCoordinateEquiv 𝕜 P).symm T
  have hscalar : scalarMatrix 𝕜 U.val s t = T.val (Pi.single t 1) s := by
    rw [← finiteCZeroOperatorEquiv_matrix]
    have he := congrArg Subtype.val ((finiteOppositeCoordinateEquiv 𝕜 P).apply_symm_apply T)
    change finiteCZeroOperatorEquiv 𝕜 P U.val = T.val at he
    rw [he]
  have hvec : (finiteCZeroSumEquiv (𝕜 := 𝕜) X).symm (Pi.single t x) = sumInjection 𝕜 X t x := by
    apply (finiteCZeroSumEquiv X).injective
    rw [LinearIsometryEquiv.apply_symm_apply, finiteCZeroSumEquiv_injection]
  change (incidenceLift h U ((finiteCZeroSumEquiv X).symm (Pi.single t x))).val s = _
  rw [hvec]
  change operatorBlock 𝕜 X X (incidenceLift h U) s t x = _
  rw [incidenceLift_block, ContinuousLinearMap.smul_apply, hscalar]

/-- Proposition 6.6 with the usual nonempty-poset convention made explicit.
The common-subspace estimate supplies contractivity; no common top space is assumed. -/
theorem proposition_6_6_proof (𝕜 : Type) [RCLike 𝕜] (P : Type)
    [Fintype P] [PartialOrder P] [Nonempty P] (X : P → Type)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] (ι : ∀ s t, X s →L[𝕜] X t) : Proposition_6_6 𝕜 P X ι := by
  intro h hcommon
  let hcols := fun T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X =>
    finite_zeroColumns (blockScalarMatrix h T)
  refine ⟨finiteOppositeCoordinateAlgebra 𝕜 P, finiteOppositeCoordinateAlgebra_carrier 𝕜 P,
    finiteScalarQuotientHom h hcommon, finiteIncidenceLiftHom h, ?_, ?_, ?_⟩
  · apply strongSplit_transport
    exact ⟨(commonScalarQuotientMap_rightInverse h hcommon hcols).surjective,
      commonScalarQuotientMap_eq_zero_iff h hcommon hcols,
      commonScalarQuotientMap_rightInverse h hcommon hcols⟩
  · exact isometry_transportSection _ _ _ _ (common_incidenceLift_isometry h hcommon hcols)
  · exact (norm_transportQuotient _ _ _ _).trans (norm_commonScalarQuotientMap h hcommon hcols)

end Posets
