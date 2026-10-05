import ThesisCommon.Analysis.ScalarPrimary
import ThesisCommon.Analysis.HilbertCotype
import ThesisCommon.Analysis.CotypeIsometry
import ThesisCommon.Analysis.CotypePreservation
import ThesisCommon.Analysis.DualCotypePreservation
import ThesisCommon.Analysis.SequencePrimariness

/-! Unconditional scalar endpoint results, used for the finite/degenerate
compact-space branches: ell1, c0 and ell-infinity have UPFP and are primary.
Scalar and dual cotype are proved from exact second moments. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem norm_scalar_operator (T : 𝕜 →L[𝕜] 𝕜) : ‖T‖ = ‖T 1‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg (T 1))
    intro z
    rw [scalar_operator_apply, norm_mul]
  · simpa only [norm_one, mul_one] using T.le_opNorm 1

theorem scalar_dual_hasFiniteCotype : HasFiniteCotype (𝕜 →L[𝕜] 𝕜) := by
  let e : (𝕜 →L[𝕜] 𝕜) →+ 𝕜 :=
    { toFun := fun T => T 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact (innerProduct_hasFiniteCotype (𝕜 := 𝕜) (H := 𝕜)).of_norm_preserving_addHom e
    (fun T => (norm_scalar_operator T).symm)

theorem scalar_ellOne_hasUPFP : HasUPFP 𝕜 (EllOneSum ℕ 𝕜) :=
  scalar_hasUPFP.ellOne_of_dualFiniteCotype scalar_dual_hasFiniteCotype

theorem scalar_cZero_hasUPFP : HasUPFP 𝕜 (CZeroSum 𝕜) :=
  scalar_hasUPFP.cZero_of_finiteCotype (innerProduct_hasFiniteCotype (𝕜 := 𝕜))

theorem scalar_infinity_hasUPFP : HasUPFP 𝕜 (EllInfinitySum 𝕜) :=
  scalar_hasUPFP.infinity_of_finiteCotype (innerProduct_hasFiniteCotype (𝕜 := 𝕜))

theorem scalar_ellOne_isPrimary : IsPrimary 𝕜 (EllOneSum ℕ 𝕜) :=
  scalar_ellOne_hasUPFP.lp_isPrimary

theorem scalar_cZero_isPrimary : IsPrimary 𝕜 (CZeroSum 𝕜) :=
  scalar_cZero_hasUPFP.cZero_isPrimary

theorem scalar_infinity_isPrimary : IsPrimary 𝕜 (EllInfinitySum 𝕜) :=
  scalar_infinity_hasUPFP.infinity_isPrimary

end ThesisCommon
