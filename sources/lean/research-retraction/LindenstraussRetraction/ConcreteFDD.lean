import LindenstraussRetraction.C0SumFDD
import LindenstraussRetraction.ConcreteConstruction
import LindenstraussRetraction.SummationApproximation

/-! The actual monotone FDDs on the renormed summation spaces and auxiliary space. -/

noncomputable section
open Filter Topology

namespace LindenstraussRetraction

universe v
variable (𝕜 : Type v) [RCLike 𝕜]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 512

local instance fddSummationNormedGroup : NormedAddCommGroup (SummationSpace 𝕜) := inferInstance
local instance fddSummationModule : Module 𝕜 (SummationSpace 𝕜) := inferInstance
local instance fddSummationNormedSpace : NormedSpace 𝕜 (SummationSpace 𝕜) := inferInstance
local instance fddRenormedNormedGroup (n : ℕ) : NormedAddCommGroup (RenormedSummationSpace 𝕜 n) := inferInstance
local instance fddRenormedModule (n : ℕ) : Module 𝕜 (RenormedSummationSpace 𝕜 n) := inferInstance
local instance fddRenormedNormedSpace (n : ℕ) : NormedSpace 𝕜 (RenormedSummationSpace 𝕜 n) := inferInstance

/-- The paper's summation-space FDD before renorming. -/
def summationMonotoneFDD : MonotoneFDD 𝕜 (SummationSpace 𝕜) where
  projection := summationApproximationOperator 𝕜
  projection_zero := summationApproximationOperator_zero 𝕜
  finite_rank := summationApproximationOperator_finite_rank 𝕜
  compatible := summationApproximationOperator_comp 𝕜
  contractive := norm_summationApproximationOperator_le 𝕜
  tendsTo_identity := summationApproximationOperator_tendsto 𝕜

/-- Conjugate the exact compatible operators `A_N` by the anisotropic equivalence. -/
def renormedSummationProjection (n N : ℕ) :
    RenormedSummationSpace 𝕜 n →L[𝕜] RenormedSummationSpace 𝕜 n :=
  (toAnisotropic (summationOperator 𝕜) (coordinateScale n)).comp
    ((summationApproximationOperator 𝕜 N).comp
      (fromAnisotropic (summationOperator 𝕜) (coordinateScale n)))

@[simp] theorem renormedSummationProjection_apply (n N : ℕ)
    (z : RenormedSummationSpace 𝕜 n) :
    renormedSummationProjection 𝕜 n N z =
      toAnisotropic (summationOperator 𝕜) (coordinateScale n)
        (summationApproximationOperator 𝕜 N
          (fromAnisotropic (summationOperator 𝕜) (coordinateScale n) z)) := rfl

theorem renormedSummationProjection_zero (n : ℕ) : renormedSummationProjection 𝕜 n 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  simp

theorem renormedSummationProjection_comp (n N M : ℕ) :
    (renormedSummationProjection 𝕜 n N).comp (renormedSummationProjection 𝕜 n M) =
      renormedSummationProjection 𝕜 n (min N M) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, renormedSummationProjection_apply,
    from_toAnisotropic _ (coordinateScale_pos n)]
  exact congrArg (toAnisotropic (summationOperator 𝕜) (coordinateScale n))
    (congrArg (fun f : SummationSpace 𝕜 →L[𝕜] SummationSpace 𝕜 =>
      f (fromAnisotropic (summationOperator 𝕜) (coordinateScale n) z))
      (summationApproximationOperator_comp 𝕜 N M))

theorem renormedSummationProjection_norm_apply_le (n N : ℕ)
    (z : RenormedSummationSpace 𝕜 n) : ‖renormedSummationProjection 𝕜 n N z‖ ≤ ‖z‖ := by
  rw [renormedSummationProjection_apply,
    norm_toAnisotropic _ (coordinateScale_pos n).le, summationOperator_approximation]
  apply max_le
  · calc
      coordinateScale n * ‖summationApproximationOperator 𝕜 N
          (fromAnisotropic (summationOperator 𝕜) (coordinateScale n) z)‖ ≤
          coordinateScale n * ‖fromAnisotropic (summationOperator 𝕜) (coordinateScale n) z‖ :=
        mul_le_mul_of_nonneg_left (summationApproximationOperator_norm_apply_le 𝕜 N _)
          (coordinateScale_pos n).le
      _ ≤ ‖z‖ := by
        have h := anisotropic_norm_lower (summationOperator 𝕜) (coordinateScale_pos n).le
          (fromAnisotropic (summationOperator 𝕜) (coordinateScale n) z)
        rwa [to_fromAnisotropic _ (coordinateScale_pos n)] at h
  · exact (norm_c0Truncation_le 𝕜 N _).trans (by
      rw [quotient_fromAnisotropic _ (coordinateScale_pos n)]
      exact anisotropicQuotient_norm_le _ _ z)

theorem renormedSummationProjection_norm_le (n N : ℕ) :
    ‖renormedSummationProjection 𝕜 n N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
    intro z
    simpa only [one_mul] using renormedSummationProjection_norm_apply_le 𝕜 n N z)

theorem renormedSummationProjection_finite_rank (n N : ℕ) :
    FiniteDimensional 𝕜 (LinearMap.range (renormedSummationProjection 𝕜 n N).toLinearMap) := by
  let Q := summationOperator 𝕜
  let ε := coordinateScale n
  let R := LinearMap.range (renormedSummationProjection 𝕜 n N).toLinearMap
  let A := LinearMap.range (summationApproximationOperator 𝕜 N).toLinearMap
  letI : FiniteDimensional 𝕜 A := summationApproximationOperator_finite_rank 𝕜 N
  let f : R →ₗ[𝕜] A :=
    ((fromAnisotropic Q ε).toLinearMap.domRestrict R).codRestrict A (by
      intro z
      obtain ⟨w, hw⟩ := z.property
      refine ⟨fromAnisotropic Q ε w, ?_⟩
      change summationApproximationOperator 𝕜 N (fromAnisotropic Q ε w) = fromAnisotropic Q ε z.val
      rw [← hw]
      change summationApproximationOperator 𝕜 N (fromAnisotropic Q ε w) =
        fromAnisotropic Q ε (toAnisotropic Q ε
          (summationApproximationOperator 𝕜 N (fromAnisotropic Q ε w)))
      rw [from_toAnisotropic Q (coordinateScale_pos n)])
  apply FiniteDimensional.of_injective f
  intro x y h
  apply Subtype.ext
  apply (anisotropicEquiv Q (coordinateScale_pos n)).symm.injective
  exact congrArg Subtype.val h

theorem renormedSummationProjection_tendsto (n : ℕ) (z : RenormedSummationSpace 𝕜 n) :
    Tendsto (fun N => renormedSummationProjection 𝕜 n N z) atTop (𝓝 z) := by
  have h := (toAnisotropic (summationOperator 𝕜) (coordinateScale n)).continuous.tendsto
    (fromAnisotropic (summationOperator 𝕜) (coordinateScale n) z)
  have ht := h.comp (summationApproximationOperator_tendsto 𝕜
    (fromAnisotropic (summationOperator 𝕜) (coordinateScale n) z))
  rwa [to_fromAnisotropic _ (coordinateScale_pos n)] at ht

/-- A monotone FDD in each renormed summation-space coordinate. -/
def renormedSummationMonotoneFDD (n : ℕ) : MonotoneFDD 𝕜 (RenormedSummationSpace 𝕜 n) where
  projection := renormedSummationProjection 𝕜 n
  projection_zero := renormedSummationProjection_zero 𝕜 n
  finite_rank := renormedSummationProjection_finite_rank 𝕜 n
  compatible := renormedSummationProjection_comp 𝕜 n
  contractive := renormedSummationProjection_norm_le 𝕜 n
  tendsTo_identity := renormedSummationProjection_tendsto 𝕜 n

/-- The diagonal finite-dimensional decomposition of the concrete auxiliary space. -/
def auxiliaryMonotoneFDD : MonotoneFDD 𝕜 (AuxiliarySpace 𝕜) :=
  c0SumMonotoneFDD 𝕜 (RenormedSummationSpace 𝕜) (renormedSummationMonotoneFDD 𝕜)

theorem auxiliary_hasMonotoneFDD : Nonempty (MonotoneFDD 𝕜 (AuxiliarySpace 𝕜)) :=
  ⟨auxiliaryMonotoneFDD 𝕜⟩

end LindenstraussRetraction
