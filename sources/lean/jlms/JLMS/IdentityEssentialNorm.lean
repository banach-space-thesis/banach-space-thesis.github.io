import JLMS.EssentialNorm
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The identity has essential norm one in infinite dimension

The lower bound uses the usual Neumann-series argument: a compact operator at
distance less than one from the identity would be invertible, making the
identity compact. Riesz's compact-unit-ball theorem then gives finite dimension.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem finiteDimensional_of_compact_identity
    (h : IsCompactOperator (ContinuousLinearMap.id 𝕜 E)) : FiniteDimensional 𝕜 E := by
  have hlin : IsCompactOperator (LinearMap.id : E →ₗ[𝕜] E) := h
  have hc := hlin.isCompact_closure_image_closedBall 1
  have heq : (LinearMap.id : E →ₗ[𝕜] E) '' Metric.closedBall (0 : E) 1 =
      Metric.closedBall (0 : E) 1 := by
    exact Set.image_id _
  rw [heq, (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : E) 1)).closure_eq] at hc
  exact FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one hc

theorem one_le_norm_identity_sub_compact [CompleteSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) (S : E →L[𝕜] E) (hS : IsCompactOperator S) :
    1 ≤ ‖ContinuousLinearMap.id 𝕜 E - S‖ := by
  by_contra h
  have hsmall : ‖1 - S‖ < 1 := lt_of_not_ge h
  have hunit : IsUnit S := by
    have hu := (Units.oneSub (1 - S) hsmall).isUnit
    simpa only [Units.val_oneSub, sub_sub_cancel] using hu
  obtain ⟨u, hu⟩ := hunit
  have hc := hS.clm_comp (↑u⁻¹ : E →L[𝕜] E)
  have heq : (↑u⁻¹ : E →L[𝕜] E).comp S = ContinuousLinearMap.id 𝕜 E := by
    change (↑u⁻¹ : E →L[𝕜] E) * S = 1
    rw [← hu]
    exact u.inv_val
  change IsCompactOperator ((↑u⁻¹ : E →L[𝕜] E).comp S) at hc
  rw [heq] at hc
  exact hE (finiteDimensional_of_compact_identity hc)

/-- No finite-dimensional or nontriviality assumptions are hidden in the
conclusion: infinite dimension is the explicit hypothesis. -/
theorem essentialNorm_identity [CompleteSpace E] (hE : ¬ FiniteDimensional 𝕜 E) :
    essentialNorm (ContinuousLinearMap.id 𝕜 E) = 1 := by
  apply le_antisymm
  · exact (essentialNorm_le_norm _).trans ContinuousLinearMap.norm_id_le
  · unfold essentialNorm
    apply le_csInf
    · exact ⟨‖ContinuousLinearMap.id 𝕜 E‖, 0, isCompactOperator_zero, by simp⟩
    · rintro r ⟨S, hS, rfl⟩
      exact one_le_norm_identity_sub_compact hE S hS

end JLMS
