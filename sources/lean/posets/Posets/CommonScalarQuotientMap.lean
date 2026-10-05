import Posets.BlockScalarRows
import Posets.CZeroMatrixOperators
import Posets.CountableSeparableBlocks
import Posets.IncidenceNorms

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P] [Nonempty P]
  {X : P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι) (hcommon : CommonSubspace 𝕜 X ι)
  (hcols : ∀ T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X, ZeroColumnsOn 𝕜 (blockScalarMatrix h T))

def commonScalarQuotientValue
    (T : DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) : oppositeIncidenceSubalgebra 𝕜 P :=
  ⟨cZeroMatrixOperator (blockScalarMatrix h T)
    (blockScalarMatrix_boundedRows h hcommon T).1 (hcols T), by
      intro s t hts
      change scalarMatrix 𝕜 (cZeroMatrixOperator _ _ _) s t = 0
      rw [scalarMatrix_cZeroMatrixOperator]
      exact blockScalarMatrix_zero_off_order h T hts⟩

theorem scalarMatrix_commonScalarQuotientValue
    (T : DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) :
    scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols T).val = blockScalarMatrix h T :=
  scalarMatrix_cZeroMatrixOperator _ _ _

theorem commonScalarQuotientValue_norm_le
    (T : DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) : ‖commonScalarQuotientValue h hcommon hcols T‖ ≤ ‖T‖ := by
  change ‖cZeroMatrixOperator (blockScalarMatrix h T)
    (blockScalarMatrix_boundedRows h hcommon T).1 (hcols T)‖ ≤ ‖T‖
  rw [norm_cZeroMatrixOperator]
  exact ciSup_le (blockScalarMatrix_boundedRows h hcommon T).2

/-- Scalar extraction under the common-subspace row bound and a column condition, before proving
its multiplicativity using the section in Lemma 6.17. -/
def commonScalarQuotientLinear :
    (DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) →ₗ[𝕜] oppositeIncidenceSubalgebra 𝕜 P :=
  { toFun := commonScalarQuotientValue h hcommon hcols
    map_add' := by
      intro T U
      apply Subtype.ext
      apply scalarMatrix_injective
      change scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols (T + U)).val =
        scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols T).val + scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols U).val
      simp only [scalarMatrix_commonScalarQuotientValue, blockScalarMatrix_add]
    map_smul' := by
      intro a T
      apply Subtype.ext
      apply scalarMatrix_injective
      change scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols (a • T)).val =
        a • scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols T).val
      simp only [scalarMatrix_commonScalarQuotientValue, blockScalarMatrix_smul]}

def commonScalarQuotientMap :
    (DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) →L[𝕜] oppositeIncidenceSubalgebra 𝕜 P :=
  LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X)
    (F := oppositeIncidenceSubalgebra 𝕜 P) (σ := RingHom.id 𝕜)
    (commonScalarQuotientLinear h hcommon hcols) 1 (fun T => by
    change ‖commonScalarQuotientValue h hcommon hcols T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using commonScalarQuotientValue_norm_le h hcommon hcols T)

theorem commonScalarQuotientMap_eq_zero_iff [Countable P]
    (T : DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) :
    commonScalarQuotientMap h hcommon hcols T = 0 ↔
      HasSeparableRange 𝕜 (DependentCZeroSum 𝕜 X)
        (DependentCZeroSum 𝕜 X) T := by
  rw [countable_blocks_separable_iff]
  rw [← blockScalarMatrix_zero_iff_blocks h]
  constructor
  · intro hz
    have hv := congrArg Subtype.val hz
    change (commonScalarQuotientValue h hcommon hcols T).val = 0 at hv
    rw [← scalarMatrix_commonScalarQuotientValue h hcommon hcols T, hv]
    rfl
  · intro hz
    apply Subtype.ext
    apply scalarMatrix_injective
    change scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols T).val = scalarMatrix 𝕜 0
    rw [scalarMatrix_commonScalarQuotientValue, hz]
    rfl

theorem norm_commonScalarQuotientMap_le : ‖commonScalarQuotientMap (𝕜 := 𝕜) (P := P) h hcommon hcols‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun T => by
      change ‖commonScalarQuotientValue h hcommon hcols T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using commonScalarQuotientValue_norm_le h hcommon hcols T)

theorem commonScalarQuotientMap_remainder
    (T : DependentCZeroSum 𝕜 X →L[𝕜]
      DependentCZeroSum 𝕜 X) (s t : P) :
    HasSeparableRange 𝕜 (X t) (X s)
      (operatorBlock 𝕜 X X T s t -
        scalarMatrix 𝕜 (commonScalarQuotientMap h hcommon hcols T).val s t • ι t s) := by
  change HasSeparableRange 𝕜 _ _ (_ - scalarMatrix 𝕜 (commonScalarQuotientValue h hcommon hcols T).val s t • _)
  rw [scalarMatrix_commonScalarQuotientValue]
  exact blockScalarMatrix_remainder h T s t

end Posets
