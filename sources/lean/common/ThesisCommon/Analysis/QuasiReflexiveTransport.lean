import ThesisCommon.Analysis.QuasiReflexiveDual
import ThesisCommon.Analysis.ResiduumDirectSums

/-! Isomorphic transport and recovery of finite quasi-reflexive order from
the dual, under finite-dimensionality of the actual defect. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem IsQuasiReflexiveOfOrder.of_equiv {n : ℕ}
    (h : IsQuasiReflexiveOfOrder 𝕜 E n) (e : E ≃L[𝕜] F) :
    IsQuasiReflexiveOfOrder 𝕜 F n := by
  letI := h.finiteDimensional
  let a := (residuumEquiv e).toLinearEquiv
  letI : FiniteDimensional 𝕜 (ResiduumSpace 𝕜 F) := a.finiteDimensional
  have hn : Module.finrank 𝕜 (ResiduumSpace 𝕜 E) = n := by
    simpa only [Module.finrank, Cardinal.toNat_natCast] using congrArg Cardinal.toNat h
  change Module.rank 𝕜 (ResiduumSpace 𝕜 F) = n
  rw [← Module.finrank_eq_rank, ← a.finrank_eq, hn]

theorem IsQuasiReflexiveOfOrder.of_dual {n : ℕ}
    [FiniteDimensional 𝕜 (ResiduumSpace 𝕜 E)]
    (h : IsQuasiReflexiveOfOrder 𝕜 (StrongDual 𝕜 E) n) :
    IsQuasiReflexiveOfOrder 𝕜 E n := by
  letI := h.finiteDimensional
  let a : StrongDual 𝕜 (ResiduumSpace 𝕜 E) ≃ₗ[𝕜]
      Module.Dual 𝕜 (ResiduumSpace 𝕜 E) := LinearMap.toContinuousLinearMap.symm
  let e := (residuumDualLinearEquiv (𝕜 := 𝕜) (X := E)).trans a
  change Module.rank 𝕜 (ResiduumSpace 𝕜 E) = n
  rw [← Module.finrank_eq_rank, ← Subspace.dual_finrank_eq,
    ← e.finrank_eq, Module.finrank_eq_rank]
  exact h

end ThesisCommon
