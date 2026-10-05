import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! The weak-star dual unit ball and the surjective restriction map induced
by an isometric embedding. Surjectivity is the actual Hahn–Banach theorem. -/
noncomputable section
open Set Topology
namespace ThesisCommon
variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

abbrev weakDualUnitBall := {φ : WeakDual 𝕜 E // ‖WeakDual.toStrongDual φ‖ ≤ 1}

instance weakDualUnitBall_compactSpace : CompactSpace (weakDualUnitBall 𝕜 E) := by
  apply isCompact_iff_compactSpace.mp
  simpa only [Set.preimage, Metric.mem_closedBall, dist_zero_right] using
    (WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 E) 1)

variable {𝕜 E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def weakDualUnitBallRestrict (i : E →ₗᵢ[𝕜] F) :
    weakDualUnitBall 𝕜 F → weakDualUnitBall 𝕜 E := fun φ =>
  ⟨StrongDual.toWeakDual ((WeakDual.toStrongDual φ.1).comp i.toContinuousLinearMap), by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖WeakDual.toStrongDual φ.1 (i x)‖ ≤ 1 * ‖x‖
    have hh := (WeakDual.toStrongDual φ.1).le_opNorm (i x)
    rw [i.norm_map] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right φ.2 (norm_nonneg x))⟩

theorem weakDualUnitBallRestrict_continuous (i : E →ₗᵢ[𝕜] F) :
    Continuous (weakDualUnitBallRestrict i) := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro x
  exact (WeakDual.eval_continuous (i x)).comp continuous_subtype_val

theorem weakDualUnitBallRestrict_surjective (i : E →ₗᵢ[𝕜] F) :
    Function.Surjective (weakDualUnitBallRestrict i) := by
  intro φ
  let e := i.equivRange
  let φr : StrongDual 𝕜 (LinearMap.range i.toLinearMap) :=
    (WeakDual.toStrongDual φ.1).comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨ψ, hψ, hnorm⟩ := exists_extension_norm_eq (LinearMap.range i.toLinearMap) φr
  have hψbound : ‖ψ‖ ≤ 1 := by
    rw [hnorm]
    change ‖(WeakDual.toStrongDual φ.1).comp e.symm.toLinearIsometry.toContinuousLinearMap‖ ≤ 1
    rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
    exact φ.2
  refine ⟨⟨StrongDual.toWeakDual ψ, hψbound⟩, ?_⟩
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change ψ (i x) = φ.1 x
  have hh := hψ (e x)
  change ψ (i x) = φ.1 (e.symm (e x)) at hh
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

end ThesisCommon
