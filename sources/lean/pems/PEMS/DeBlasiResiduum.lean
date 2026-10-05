import PEMS.DeBlasiProperties
import ThesisCommon.Analysis.WeakCompactApproximationBidual
import ThesisCommon.Analysis.ResiduumProperties

/-! The actual residuum norm is bounded by the actual De Blasi measure.
Weakly compact approximation passes to the bidual by Goldstine and
Banach--Alaoglu; quotient norms then retain the same sharp constant. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open Set Topology ThesisCommon
namespace PEMS
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem residuumNorm_le_of_weakCompact_approximation
    (T : E →L[𝕜] F) (D : Set F) (hD : IsCompact (toWeakSpace 𝕜 F '' D))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcover : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ D, ‖T x-y‖ ≤ ε) :
    residuumNorm T ≤ ε := by
  let L : StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] ResiduumSpace 𝕜 F :=
    { toLinearMap := (bidualImage 𝕜 F).mkQ.comp (bidualMap T).toLinearMap
      cont := continuous_quot_mk.comp (bidualMap T).continuous }
  have hL : ‖L‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
    intro ξ hξ
    obtain ⟨y, _, hy⟩ := exists_bidual_weakCompact_approximation T D hD hcover ξ hξ.le
    have hj : (Submodule.Quotient.mk (NormedSpace.inclusionInDoubleDual 𝕜 F y) :
        ResiduumSpace 𝕜 F) = 0 :=
      (Submodule.Quotient.mk_eq_zero (p := bidualImage 𝕜 F)).mpr ⟨y, rfl⟩
    have heq : (Submodule.Quotient.mk
        (bidualMap T ξ - NormedSpace.inclusionInDoubleDual 𝕜 F y) : ResiduumSpace 𝕜 F) = L ξ := by
      rw [Submodule.Quotient.mk_sub, hj, sub_zero]
      rfl
    rw [← heq]
    exact (Submodule.Quotient.norm_mk_le _ _).trans hy
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro z
  apply le_of_forall_pos_le_add
  intro δ hδ
  let η := δ/(ε+1)
  have hη : 0 < η := div_pos hδ (by positivity)
  obtain ⟨ξ, hξ, hnξ⟩ := Submodule.Quotient.norm_mk_lt z hη
  have hsmall : ε * η ≤ δ := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < ε+1)).mpr
    nlinarith
  calc
    ‖residuumOperator T z‖ = ‖L ξ‖ := by rw [← hξ]; rfl
    _ ≤ ‖L‖ * ‖ξ‖ := L.le_opNorm ξ
    _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg ξ)
    _ ≤ ε * (‖z‖+η) := mul_le_mul_of_nonneg_left hnξ.le hε
    _ ≤ ε * ‖z‖ + δ := by nlinarith

theorem residuumNorm_le_deBlasiOperator (T : E →L[𝕜] F) :
    residuumNorm T ≤ deBlasiOperator T := by
  apply le_csInf
  · refine ⟨‖T‖ + 1, by positivity, {0}, by simp, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    refine ⟨0, by simp, ?_⟩
    simpa using ((T.le_opNorm x).trans
      (mul_le_of_le_one_right (norm_nonneg T) hx')).trans (by linarith : ‖T‖ ≤ ‖T‖+1)
  · rintro ε ⟨hε, D, hD, hcover⟩
    apply residuumNorm_le_of_weakCompact_approximation T D hD hε.le
    intro x hx
    exact hcover (T x) ⟨x, by simpa using hx, rfl⟩

end PEMS
