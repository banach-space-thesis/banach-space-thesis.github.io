import ThesisCommon.Analysis.ResiduumNormLaws
import ThesisCommon.Analysis.CZeroAdjointFactorization
import ThesisCommon.Analysis.CZeroInfinityEmbedding
import ThesisCommon.Analysis.AdjointWeakEssentialNorm

/-! Sharp residuum lower bounds from nonreflexive identity factorizations.
The normalization on actual scalar ell-infinity is proved using its actual
isometric c0 subspace and the adjoint factorization estimate. -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option synthInstance.maxSize 1024
namespace ThesisCommon
variable {𝕜 E F Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem residuumNorm_id_eq_one_of_nonweaklyCompact [CompleteSpace Z]
    (h : ¬IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z)) :
    residuumNorm (ContinuousLinearMap.id 𝕜 Z) = 1 := by
  have hn := residuumNorm_nonneg (ContinuousLinearMap.id 𝕜 Z)
  have hp : 0 < residuumNorm (ContinuousLinearMap.id 𝕜 Z) :=
    lt_of_le_of_ne hn (Ne.symm fun hz => h ((residuumNorm_eq_zero_iff _).mp hz))
  have hle := (residuumNorm_le_norm (ContinuousLinearMap.id 𝕜 Z)).trans
    ContinuousLinearMap.norm_id_le
  have hmul := residuumNorm_comp_le (ContinuousLinearMap.id 𝕜 Z)
    (ContinuousLinearMap.id 𝕜 Z)
  rw [ContinuousLinearMap.id_comp] at hmul
  nlinarith

theorem scalarInfinity_identity_not_weaklyCompact :
    ¬IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜)) := by
  intro h
  have hb := cZero_lower_bound_le_adjoint_weakEssentialNorm
    (ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜))
    (cZeroToInfinityIsometry (𝕜 := 𝕜)).toContinuousLinearMap
    (cZeroToInfinityIsometry (𝕜 := 𝕜)).norm_toContinuousLinearMap_le
    (c := 1) zero_le_one (fun x => by
      simpa only [one_mul, ContinuousLinearMap.id_apply] using
        (cZeroToInfinityIsometry (𝕜 := 𝕜)).norm_map x |>.ge)
  have hle := weakEssentialNorm_banachAdjoint_le (ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜))
  rw [h.weakEssentialNorm_eq_zero] at hle
  linarith

theorem residuumNorm_id_scalarInfinity :
    residuumNorm (ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜)) = 1 :=
  residuumNorm_id_eq_one_of_nonweaklyCompact scalarInfinity_identity_not_weaklyCompact

theorem factorization_constant_le_residuumNorm
    (hZ : residuumNorm (ContinuousLinearMap.id 𝕜 Z) = 1)
    (T : E →L[𝕜] F) (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (hfac : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z) :
    ‖U‖⁻¹ * ‖V‖⁻¹ ≤ residuumNorm T := by
  have hb : 1 ≤ (‖U‖ * ‖V‖) * residuumNorm T := by
    calc
      1 = residuumNorm (U.comp (T.comp V)) := by rw [hfac, hZ]
      _ ≤ ‖U‖ * residuumNorm (T.comp V) := residuumNorm_comp_left_le _ _
      _ ≤ ‖U‖ * (residuumNorm T * ‖V‖) :=
        mul_le_mul_of_nonneg_left (residuumNorm_comp_right_le _ _) (norm_nonneg U)
      _ = _ := by ring
  have hp : 0 < ‖U‖ * ‖V‖ := by
    by_contra h
    have hz := le_antisymm (not_lt.mp h) (mul_nonneg (norm_nonneg U) (norm_nonneg V))
    rw [hz, zero_mul] at hb
    norm_num at hb
  rw [← mul_inv]
  exact (inv_le_iff_one_le_mul₀' hp).mpr hb

end ThesisCommon
