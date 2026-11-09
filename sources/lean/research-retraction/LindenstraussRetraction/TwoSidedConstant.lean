import LindenstraussRetraction.AmplificationCore
import LindenstraussRetraction.SummationBidualProjection
import LindenstraussRetraction.AuxiliaryNoRetraction

/-! The actual two-sided Lipschitz retraction bounds of Section 4. -/

noncomputable section

namespace LindenstraussRetraction

universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

local instance twoSidedAnisotropicNormedSpace (Q : Y →L[𝕜] W) (ε : ℝ) :
    NormedSpace 𝕜 (AnisotropicSpace Q ε) :=
  Submodule.normedSpace (𝕜 := 𝕜) (R := 𝕜) (E := Y × W) (AnisotropicSpace Q ε)

local instance twoSidedBidualNormedGroup (X : Type u)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : NormedAddCommGroup (Bidual 𝕜 X) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := StrongDual 𝕜 X) (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

/-- Transport the projection along the equivalent graph renorming. -/
def anisotropicBidualProjection (Q : Y →L[𝕜] W) (ε : ℝ)
    (P : Bidual 𝕜 Y →L[𝕜] Y) :
    Bidual 𝕜 (AnisotropicSpace Q ε) →L[𝕜] AnisotropicSpace Q ε :=
  ((toAnisotropic Q ε).comp P).comp (bidualMap (fromAnisotropic Q ε))

theorem anisotropicBidualProjection_norm_le
    (Q : Y →L[𝕜] W) (hQ : ∀ y, ‖Q y‖ ≤ ‖y‖) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (P : Bidual 𝕜 Y →L[𝕜] Y)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (z : Bidual 𝕜 (AnisotropicSpace Q ε)) :
    ‖anisotropicBidualProjection Q ε P z‖ ≤ ε⁻¹ * ‖z‖ := by
  have hfrom : ‖fromAnisotropic Q ε‖ ≤ ε⁻¹ :=
    (fromAnisotropic Q ε).opNorm_le_bound (inv_nonneg.mpr hε.le)
      (norm_fromAnisotropic_le Q hε)
  calc
    ‖anisotropicBidualProjection Q ε P z‖ ≤
        ‖P (bidualMap (fromAnisotropic Q ε) z)‖ := by
      rw [anisotropicBidualProjection, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, norm_toAnisotropic Q hε.le]
      exact max_le (by nlinarith [norm_nonneg (P (bidualMap (fromAnisotropic Q ε) z))]) (hQ _)
    _ ≤ ‖bidualMap (fromAnisotropic Q ε) z‖ := hP _
    _ ≤ ‖fromAnisotropic Q ε‖ * ‖z‖ := norm_bidualMap_apply_le _ _
    _ ≤ ε⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_right hfrom (norm_nonneg z)

theorem anisotropicBidualProjection_embedding
    (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 < ε)
    (P : Bidual 𝕜 Y →L[𝕜] Y) (hfix : ∀ y, P (bidualEmbedding 𝕜 Y y) = y)
    (y : AnisotropicSpace Q ε) :
    anisotropicBidualProjection Q ε P (bidualEmbedding 𝕜 (AnisotropicSpace Q ε) y) = y := by
  change toAnisotropic Q ε (P (bidualMap (fromAnisotropic Q ε)
    (bidualEmbedding 𝕜 (AnisotropicSpace Q ε) y))) = y
  rw [bidualMap_embedding, hfix, to_fromAnisotropic Q hε]

theorem anisotropic_retractionConstant_upper
    (Q : Y →L[𝕜] W) (hQ : ∀ y, ‖Q y‖ ≤ ‖y‖) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (P : Bidual 𝕜 Y →L[𝕜] Y)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (hfix : ∀ y, P (bidualEmbedding 𝕜 Y y) = y) :
    bidualLipschitzRetractionConstant 𝕜 (AnisotropicSpace Q ε) ≤ ENNReal.ofReal ε⁻¹ := by
  let K : NNReal := ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩
  have hLip : LipschitzWith K (anisotropicBidualProjection Q ε P) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact anisotropicBidualProjection_norm_le Q hQ hε hε1 P hP _
  have hmem : (K : ENNReal) ∈ {L : ENNReal | ∃ (K : NNReal)
      (r : Bidual 𝕜 (AnisotropicSpace Q ε) → AnisotropicSpace Q ε),
      L = K ∧ LipschitzWith K r ∧ IsRetraction (bidualEmbedding 𝕜 _) r} :=
    ⟨K, anisotropicBidualProjection Q ε P, rfl, hLip,
      anisotropicBidualProjection_embedding Q hε P hfix⟩
  change sInf _ ≤ _
  have hcoerce : (K : ENNReal) = ENNReal.ofReal ε⁻¹ := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  exact (sInf_le hmem).trans_eq hcoerce

variable (𝕜)

theorem coordinateScale_inverse (n : ℕ) : (coordinateScale n)⁻¹ = (2 : ℝ) ^ (n+1) := by
  simp only [coordinateScale, one_div, inv_pow, inv_inv]

theorem coordinateScale_amplification (n : ℕ) :
    1 / (coordinateScale n * (1 + 1)) = (2 : ℝ) ^ n := by
  rw [one_div, mul_inv_rev, coordinateScale_inverse, pow_succ]
  ring

theorem twoSidedRetractionConstant : TwoSidedRetractionConstantStatement 𝕜 := by
  intro n
  constructor
  · apply le_sInf
    rintro L ⟨K, R, rfl, hR, hfix⟩
    have hLower := amplification_lipschitz_constant_lower
      (summationOperator 𝕜) (summationOperator_isNormQuotient 𝕜)
      (no_uniformSection_summationOperator 𝕜) (summationBidualLift 𝕜)
      (M := 1) (ε := coordinateScale n) (by norm_num) (coordinateScale_pos n)
      (fun x => by simpa only [one_mul, norm_summationBidualLift] using le_refl ‖x‖)
      (summationBidualLift_rightInverse 𝕜) K R hR hfix
    rw [coordinateScale_amplification n] at hLower
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hLower
  · have hUpper := anisotropic_retractionConstant_upper (summationOperator 𝕜)
      (fun y => (summationOperator_isNormQuotient 𝕜).norm_le y)
      (coordinateScale_pos n) ((coordinateScale_le_half n).trans (by norm_num))
      (summationBidualProjection 𝕜) (norm_summationBidualProjection_le 𝕜)
      (summationBidualProjection_embedding 𝕜)
    simpa only [coordinateScale_inverse] using hUpper

end LindenstraussRetraction

