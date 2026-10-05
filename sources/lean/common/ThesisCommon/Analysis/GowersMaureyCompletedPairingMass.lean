import ThesisCommon.Analysis.GowersMaureyCompletedPairing
import ThesisCommon.Analysis.GowersMaureyRationalApproximation

/-! Coefficient-mass error estimates for finite functionals acting on the
actual completion. These estimates transfer the constructed Gaussian-rational
approximations to operator evaluations without assuming finite images. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem completedPairing_norm_le_mass_mul (D : ConstructionData 𝕜)
    (a : C00 𝕜) (x : ShiftSpace D) :
    ‖completedPairing D a x‖ ≤ mass a * ‖x‖ := by
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_le (completedPairing D a).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro y
    rw [completedPairing_denseEmbedding, denseEmbedding_norm]
    exact pairing_norm_le_mass_mul_implicitNorm D a y

theorem completedPairing_sub_norm_le_mass_mul (D : ConstructionData 𝕜)
    (a b : C00 𝕜) (x : ShiftSpace D) :
    ‖completedPairing D a x - completedPairing D b x‖ ≤ mass (a-b) * ‖x‖ := by
  simpa only [map_sub, ContinuousLinearMap.sub_apply] using
    completedPairing_norm_le_mass_mul D (a-b) x

end ThesisCommon.GowersMaurey
