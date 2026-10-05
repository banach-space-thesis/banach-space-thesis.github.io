import Posets.IncidenceLift
import Posets.CommonScalarQuotientNorm
import PosetsCommon.SeparableOperatorIdeal

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem blockScalarMatrix_incidenceLift {P : Type} [PartialOrder P] [Nonempty P]
    {X : P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] {ι : ∀ s t, X s →L[𝕜] X t}
    (h : FewOperators 𝕜 X ι) (T : oppositeIncidenceSubalgebra 𝕜 P) :
    blockScalarMatrix h (incidenceLift h T) = scalarMatrix 𝕜 T.val := by
  classical
  funext s t
  by_cases hts : t ≤ s
  · simp only [blockScalarMatrix, dif_pos hts, incidenceLift_block]
    change scalarBetween (fewOperators_scalarDecompositions h hts)
      (scalarMatrix 𝕜 T.val s t • ι t s) = _
    rw [scalarBetween_smul (h.1 t) (h.2.1 t s hts),
      scalarBetween_embedding (h.1 t) (h.2.1 t s hts)]
    simp
  · simp only [blockScalarMatrix, dif_neg hts, T.property s t hts]

variable {P : Type} [PartialOrder P] [Nonempty P]
  {X : P → Type} [∀ p, NormedAddCommGroup (X p)]
  [∀ p, NormedSpace 𝕜 (X p)] [∀ p, CompleteSpace (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι) (hcommon : CommonSubspace 𝕜 X ι)
  (hcols : ∀ T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X, ZeroColumnsOn 𝕜 (blockScalarMatrix h T))

theorem commonScalarQuotientMap_rightInverse :
    Function.RightInverse (incidenceLift h) (commonScalarQuotientMap h hcommon hcols) := by
  intro T
  apply Subtype.ext
  apply scalarMatrix_injective
  change scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols (incidenceLift h T)).val = _
  rw [scalarMatrix_commonScalarQuotientValue, blockScalarMatrix_incidenceLift]

include hcommon hcols in
theorem common_norm_incidenceLift (T : oppositeIncidenceSubalgebra 𝕜 P) :
    ‖incidenceLift h T‖ = ‖T‖ := by
  apply le_antisymm (incidenceLiftValue_norm_le h T)
  have hb := commonScalarQuotientValue_norm_le h hcommon hcols (incidenceLift h T)
  change ‖commonScalarQuotientMap h hcommon hcols (incidenceLift h T)‖ ≤ _ at hb
  rwa [commonScalarQuotientMap_rightInverse h hcommon hcols T] at hb

include hcommon hcols in
theorem common_incidenceLift_isometry : Isometry (incidenceLift h) :=
  AddMonoidHomClass.isometry_of_norm (incidenceLift h) (common_norm_incidenceLift h hcommon hcols)

theorem commonScalarQuotientMap_mul [Countable P]
    (S T : DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) :
    commonScalarQuotientMap h hcommon hcols (S * T) = commonScalarQuotientMap h hcommon hcols S * commonScalarQuotientMap h hcommon hcols T := by
  apply multiplicative_of_section (commonScalarQuotientMap h hcommon hcols).toLinearMap
    (separableOperatorIdeal 𝕜 (DependentCZeroSum 𝕜 X))
    (fun U => (commonScalarQuotientMap_eq_zero_iff h hcommon hcols U).trans (mem_separableOperatorIdeal _ _ U).symm)
    (incidenceLift h) (incidenceLift_mul h)
    (commonScalarQuotientMap_rightInverse h hcommon hcols)

def commonScalarQuotientHom [Countable P] : BoundedHom 𝕜
    (DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) (oppositeIncidenceSubalgebra 𝕜 P) where
  toContinuousLinearMap := commonScalarQuotientMap h hcommon hcols
  map_mul' := commonScalarQuotientMap_mul h hcommon hcols


end Posets
