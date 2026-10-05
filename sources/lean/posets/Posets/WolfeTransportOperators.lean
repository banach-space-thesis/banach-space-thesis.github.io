import Posets.WolfeTransport
import Posets.SzlenkIdealComposition

/-! Wolfe transport for the actual adjoint unit ball of an operator. Isometric
changes of target coordinates preserve that ball; homeomorphic changes of
domain coordinates preserve every Wolfe level with its original threshold. -/

noncomputable section
open Set Topology ThesisCommon
universe u
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

section DualBall
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem weakStarAdjoint_isometry_norm_le (e : E →ₗᵢ[𝕜] F) (μ : WeakDual 𝕜 F) :
    ‖WeakDual.toStrongDual (weakStarAdjoint e.toContinuousLinearMap μ)‖ ≤
      ‖WeakDual.toStrongDual μ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖μ (e x)‖ ≤ _
  simpa only [e.norm_map] using (WeakDual.toStrongDual μ).le_opNorm (e x)

theorem weakStarAdjoint_isometryEquiv_unitBall (e : E ≃ₗᵢ[𝕜] F) :
    weakStarAdjoint e.toContinuousLinearEquiv.toContinuousLinearMap '' weakStarUnitBall 𝕜 F =
      weakStarUnitBall 𝕜 E := by
  have hin (e : E →ₗᵢ[𝕜] F) (μ : WeakDual 𝕜 F) (hμ : μ ∈ weakStarUnitBall 𝕜 F) :
      weakStarAdjoint e.toContinuousLinearMap μ ∈ weakStarUnitBall 𝕜 E := by
    have hnorm : ‖WeakDual.toStrongDual μ‖ ≤ 1 := by
      simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hμ
    simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using
      (weakStarAdjoint_isometry_norm_le e μ).trans hnorm
  apply Set.Subset.antisymm
  · rintro _ ⟨μ, hμ, rfl⟩
    exact hin e.toLinearIsometry μ hμ
  · intro μ hμ
    let ν := weakStarAdjoint e.symm.toContinuousLinearEquiv.toContinuousLinearMap μ
    refine ⟨ν, ?_, ?_⟩
    · have hnorm : ‖WeakDual.toStrongDual μ‖ ≤ 1 := by
        simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hμ
      simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using
        (weakStarAdjoint_isometry_norm_le e.symm.toLinearIsometry μ).trans hnorm
    · apply DFunLike.ext
      intro x
      change μ (e.symm (e x)) = μ x
      rw [e.symm_apply_apply]

theorem adjointUnitBall_postcomp_isometryEquiv (T : E →L[𝕜] F) (e : F ≃ₗᵢ[𝕜] G) :
    adjointUnitBall (e.toContinuousLinearEquiv.toContinuousLinearMap.comp T) = adjointUnitBall T := by
  rw [adjointUnitBall_comp]
  change weakStarAdjoint T ''
    (weakStarAdjoint e.toContinuousLinearEquiv.toContinuousLinearMap '' weakStarUnitBall 𝕜 G) = _
  rw [weakStarAdjoint_isometryEquiv_unitBall]
  rfl

end DualBall

variable {K L X Y : Type*} [TopologicalSpace K] [TopologicalSpace L]
  [LocallyCompactSpace K] [LocallyCompactSpace L] [T2Space K] [T2Space L]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem wolfeFamily_operator_transport_nonempty_iff
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (hK : JLMS.IsScattered K) (hL : JLMS.IsScattered L)
    (e : K ≃ₜ L) (f : X ≃ₗᵢ[𝕜] Y) (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    (ε : ℝ) (α : Ordinal.{u}) :
    (wolfeFamily N ε (adjointUnitBall
      (f.toContinuousLinearEquiv.toContinuousLinearMap.comp (T.comp (cZeroHomeomorphPull e)))) α).Nonempty ↔
      (wolfeFamily M ε (adjointUnitBall T) α).Nonempty := by
  rw [adjointUnitBall_postcomp_isometryEquiv, adjointUnitBall_comp]
  exact wolfeFamily_homeomorph_nonempty_iff M N hK hL e ε (adjointUnitBall T) α

end Posets
