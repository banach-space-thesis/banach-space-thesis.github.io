import ThesisCommon.Analysis.QuantitativeSequenceDecomposition
import ThesisCommon.Analysis.FactorNormalization

/-! A uniform polynomial estimate for a factorisation through a projection
on an isometrically sequence-stable space. This generous estimate is derived
from actual splitting maps; it is not the printed Appendix A formula. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem equivOfRightInverse_normBound (U : X →L[𝕜] Y) (V : Y →L[𝕜] X)
    (hUV : Function.RightInverse V U) {u v D : ℝ}
    (_hu : 0 ≤ u) (hv : 0 ≤ v) (hU : ‖U‖ ≤ u) (hV : ‖V‖ ≤ v)
    (huD : u ≤ D) (hvuD : 1 + v * u ≤ D) (hvD : v + 1 ≤ D) :
    EquivNormBound (ContinuousLinearEquiv.equivOfRightInverse U V hUV) D := by
  have hUx (x : X) : ‖U x‖ ≤ u * ‖x‖ :=
    (U.le_opNorm x).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg x))
  have hVx (y : Y) : ‖V y‖ ≤ v * ‖y‖ :=
    (V.le_opNorm y).trans (mul_le_mul_of_nonneg_right hV (norm_nonneg y))
  constructor
  · intro x
    apply max_le
    · exact (hUx x).trans (mul_le_mul_of_nonneg_right huD (norm_nonneg x))
    · change ‖x - V (U x)‖ ≤ D * ‖x‖
      calc
        _ ≤ ‖x‖ + ‖V (U x)‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + v * (u * ‖x‖) := add_le_add_left
          ((hVx _).trans (mul_le_mul_of_nonneg_left (hUx x) hv)) _
        _ = (1 + v * u) * ‖x‖ := by ring
        _ ≤ D * ‖x‖ := mul_le_mul_of_nonneg_right hvuD (norm_nonneg x)
  · intro y
    change ‖V y.1 + (y.2 : X)‖ ≤ D * ‖y‖
    calc
      _ ≤ ‖V y.1‖ + ‖(y.2 : X)‖ := norm_add_le _ _
      _ ≤ v * ‖y‖ + ‖y‖ := add_le_add
        ((hVx y.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le y) hv)) (norm_snd_le y)
      _ = (v + 1) * ‖y‖ := by ring
      _ ≤ D * ‖y‖ := mul_le_mul_of_nonneg_right hvD (norm_nonneg y)

def projectionFactorDecompositionBound (L K : ℝ) : ℝ :=
  1024 * (2 + L + K + L * K) ^ 10

theorem projectionFactorDecompositionBound_mono {L₁ L₂ K₁ K₂ : ℝ}
    (hL₁ : 0 ≤ L₁) (hK₁ : 0 ≤ K₁) (hL : L₁ ≤ L₂) (hK : K₁ ≤ K₂) :
    projectionFactorDecompositionBound L₁ K₁ ≤ projectionFactorDecompositionBound L₂ K₂ := by
  unfold projectionFactorDecompositionBound
  gcongr
  exact hL₁.trans hL

theorem one_le_projectionFactorDecompositionBound {L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) : 1 ≤ projectionFactorDecompositionBound L K := by
  have hD : 1 ≤ 2 + L + K + L * K := by nlinarith [mul_nonneg hL hK]
  have hp : 1 ≤ (2 + L + K + L * K) ^ 10 := one_le_pow₀ hD
  unfold projectionFactorDecompositionBound
  linarith

/-- A genuine factorisation through a projection yields an attained bounded
equivalence with its actual range. No nonzero-space hypothesis is required. -/
theorem FactorsIdentityWith.projection_range_isomorphic_of_lp_isometry
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (eX : X ≃ₗᵢ[𝕜] lp (fun _ : ℕ => X) p)
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
  have h := (lpDecompositionEquiv_normBound p eX.toContinuousLinearEquiv eXY eYX
    hD (equivNormBound_isometry eX) hXY hYX).isomorphicWithBound (by positivity)
  convert h using 1
  dsimp [projectionFactorDecompositionBound, D]
  ring

end ThesisCommon
