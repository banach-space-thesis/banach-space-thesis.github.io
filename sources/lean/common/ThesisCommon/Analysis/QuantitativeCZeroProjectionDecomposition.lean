import ThesisCommon.Analysis.QuantitativeCZeroDecomposition
import ThesisCommon.Analysis.QuantitativeProjectionDecomposition

/-! An explicit uniform bound for a factorisation through a projection on an
isometrically c₀-stable space. This estimate comes from actual splitting and
sequence rearrangement maps and includes degenerate spaces and projections. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
/-- A genuine factorisation through a projection yields an attained bounded
equivalence with its actual range. No nonzero-space hypothesis is required. -/
theorem FactorsIdentityWith.projection_range_isomorphic_of_cZero_isometry
    (eX : X ≃ₗᵢ[𝕜] CZeroSum X)
    {P : X →L[𝕜] X} (hP : P.comp P = P) {L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hPL : ‖P‖ ≤ L)
    (hf : FactorsIdentityWith P X K) :
    IsomorphicWithBound 𝕜 X (LinearMap.range P.toLinearMap)
      (projectionFactorDecompositionBound L K) := by
  obtain ⟨U, V, hUV, hU, hV⟩ := hf.normalized
  let R := LinearMap.range P.toLinearMap
  have hPfix (y : R) : P y = y := by
    obtain ⟨x, hx⟩ := y.property
    change P x = y.val at hx
    rw [← hx]
    exact DFunLike.congr_fun hP x
  let eXY := ContinuousLinearEquiv.equivOfRightInverse P.rangeRestrict R.subtypeL
    (fun y => Subtype.ext (hPfix y))
  let U' : R →L[𝕜] X := U.comp R.subtypeL
  let V' : X →L[𝕜] R := P.rangeRestrict.comp V
  have hU' : ‖U'‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro y
    exact (U.le_opNorm y.val).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg y))
  have hV' : ‖V'‖ ≤ L := by
    apply ContinuousLinearMap.opNorm_le_bound _ hL
    intro x
    change ‖P (V x)‖ ≤ L * ‖x‖
    have hvx : ‖V x‖ ≤ ‖x‖ := by
      simpa only [one_mul] using (V.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hV (norm_nonneg x))
    exact (P.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hPL (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hvx hL))
  have hU'V' : Function.RightInverse V' U' := fun x => DFunLike.congr_fun hUV x
  let eYX := ContinuousLinearEquiv.equivOfRightInverse U' V' hU'V'
  let D : ℝ := 2 + L + K + L * K
  have hLK : 0 ≤ L * K := mul_nonneg hL hK
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hXY : EquivNormBound eXY D := by
    apply equivOfRightInverse_normBound P.rangeRestrict R.subtypeL _ hL zero_le_one
    · apply ContinuousLinearMap.opNorm_le_bound _ hL
      intro x
      exact (P.le_opNorm x).trans (mul_le_mul_of_nonneg_right hPL (norm_nonneg x))
    · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro y
      simp
    · dsimp [D]; linarith
    · dsimp [D]; linarith
    · dsimp [D]; linarith
  have hYX : EquivNormBound eYX D := by
    apply equivOfRightInverse_normBound U' V' hU'V' hK hL hU' hV'
    · dsimp [D]; linarith
    · dsimp [D]; linarith
    · dsimp [D]; linarith
  have h := (cZeroDecompositionEquiv_normBound eX.toContinuousLinearEquiv eXY eYX
    hD (equivNormBound_isometry eX) hXY hYX).isomorphicWithBound (by positivity)
  convert h using 1
  dsimp [projectionFactorDecompositionBound, D]
  ring

end ThesisCommon

