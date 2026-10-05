import Posets.SzlenkPerturbationIterate

/-! Norm-closedness of the actual operator Szlenk classes. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem adjointUnitBall_perturbation (T S : E →L[𝕜] F) :
    ∀ a ∈ adjointUnitBall T, ∃ b ∈ adjointUnitBall S,
      ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤ ‖T - S‖ := by
  rintro a ⟨φ, hφ, rfl⟩
  refine ⟨weakStarAdjoint S φ, ⟨φ, hφ, rfl⟩, ?_⟩
  have hφnorm : ‖WeakDual.toStrongDual φ‖ ≤ 1 := by
    simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hφ
  change ‖(WeakDual.toStrongDual φ).comp T - (WeakDual.toStrongDual φ).comp S‖ ≤ _
  rw [← ContinuousLinearMap.comp_sub]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hφnorm (norm_nonneg (T - S)))

theorem isClosed_operatorSzlenkBound (α : Ordinal) :
    IsClosed {T : E →L[𝕜] F | OperatorSzlenkBound T α} := by
  apply isClosed_of_closure_subset
  intro T hT
  intro ε hε
  have hball : T ∈ Metric.ball T (ε / 8) := Metric.mem_ball_self (by positivity)
  obtain ⟨S, hSball, hS⟩ := mem_closure_iff.mp hT _ Metric.isOpen_ball hball
  have hnear : ∀ a ∈ adjointUnitBall T, ∃ b ∈ adjointUnitBall S,
      ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤ ε / 8 := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := adjointUnitBall_perturbation T S a ha
    have hTS : ‖T - S‖ < ε / 8 := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hSball
    exact ⟨b, hb, hab.trans hTS.le⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, hy, _⟩ := szlenkIterate_perturbation (adjointUnitBall_isCompact S)
    (show ε / 4 + 2 * (ε / 8) ≤ ε / 2 by linarith) hnear α x hx
  have hSz := hS (ε / 4) (by positivity)
  rw [hSz] at hy
  exact hy

theorem isClosed_szlenkOperatorClass (α : Ordinal) :
    IsClosed (SzlenkOperatorClass (𝕜 := 𝕜) (E := E) (F := F) α) :=
  isClosed_operatorSzlenkBound (Ordinal.omega0 ^ α)

end Posets
