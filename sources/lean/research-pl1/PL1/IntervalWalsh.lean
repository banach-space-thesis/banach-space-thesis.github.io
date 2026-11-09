import PL1.IntervalRetraction
import PL1.IntervalSubtype
import PL1.ProjectionRetract

/-!
# Actual interval transport for the Walsh ell1 ambient space

The maps are constructed through the explicit geometric probability model,
a measurable interval sampler, and its regular conditional distribution.
The resulting interval projection does not need an assumed ambient isomorphism.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PL1.IntervalWalsh

variable (𝕜 : Type*) [RCLike 𝕜]

/-- Concrete isometric embedding of the Walsh ell1 ambient space in interval L1. -/
def walshSumEmbedding : L1Sum (Lp 𝕜 1 Walsh.haar) →ₗᵢ[𝕜] IntervalL1 𝕜 :=
  (IntervalSubtype.equiv 𝕜).toLinearIsometry.comp
    ((IntervalRetraction.pullback (IntervalModel.probabilityMeasure Walsh.haar)).comp
      IntervalModel.walshSumProbabilityEquiv.toLinearIsometry)

/-- Concrete averaging retraction from interval L1 to the Walsh ell1 ambient space. -/
def walshSumRetraction : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 Walsh.haar) :=
  IntervalModel.walshSumProbabilityEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((IntervalRetraction.retraction (IntervalModel.probabilityMeasure Walsh.haar)).comp
      (IntervalSubtype.equiv 𝕜).symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem walshSumRetraction_embedding (x : L1Sum (Lp 𝕜 1 Walsh.haar)) :
    walshSumRetraction 𝕜 (walshSumEmbedding 𝕜 x) = x := by
  change IntervalModel.walshSumProbabilityEquiv.symm
    (IntervalRetraction.retraction (IntervalModel.probabilityMeasure Walsh.haar)
      ((IntervalSubtype.equiv 𝕜).symm ((IntervalSubtype.equiv 𝕜)
        (IntervalRetraction.pullback (IntervalModel.probabilityMeasure Walsh.haar)
          (IntervalModel.walshSumProbabilityEquiv x))))) = x
  rw [LinearIsometryEquiv.symm_apply_apply, IntervalRetraction.retraction_pullback,
    LinearIsometryEquiv.symm_apply_apply]

theorem norm_walshSumRetraction_le : ‖walshSumRetraction 𝕜‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖IntervalModel.walshSumProbabilityEquiv.symm
    (IntervalRetraction.retraction (IntervalModel.probabilityMeasure Walsh.haar)
      ((IntervalSubtype.equiv 𝕜).symm x))‖ ≤ 1 * ‖x‖
  rw [LinearIsometryEquiv.norm_map, one_mul]
  calc
    _ ≤ ‖IntervalRetraction.retraction (𝕜 := 𝕜) (IntervalModel.probabilityMeasure Walsh.haar)‖ *
        ‖(IntervalSubtype.equiv 𝕜).symm x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖(IntervalSubtype.equiv 𝕜).symm x‖ :=
      mul_le_mul_of_nonneg_right (IntervalRetraction.norm_retraction_le _) (norm_nonneg _)
    _ = ‖x‖ := by rw [one_mul, LinearIsometryEquiv.norm_map]

/-- The concrete contractive retract needed to transport either actual projection
onto the reviewed interval L1 space, over both real and complex scalars. -/
def walshSumContractiveRetract :
    ContractiveRetract 𝕜 (L1Sum (Lp 𝕜 1 Walsh.haar)) (IntervalL1 𝕜) where
  embedding := walshSumEmbedding 𝕜
  retraction := walshSumRetraction 𝕜
  left_inv := walshSumRetraction_embedding 𝕜
  norm_retraction_le := norm_walshSumRetraction_le 𝕜

end PL1.IntervalWalsh

