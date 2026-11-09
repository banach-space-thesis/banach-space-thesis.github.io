import LindenstraussRetraction.RenormedRetractionObstruction
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Data.ENNReal.Real

/-! # Quantitative amplification of the bidual retraction constant -/

noncomputable section

namespace LindenstraussRetraction

universe u v w s

variable {𝕜 : Type s} [RCLike 𝕜]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

local instance amplificationAnisotropicNormedSpace (Q : Y →L[𝕜] W) (ε : ℝ) :
    NormedSpace 𝕜 (AnisotropicSpace Q ε) :=
  Submodule.normedSpace (𝕜 := 𝕜) (R := 𝕜) (E := Y × W) (AnisotropicSpace Q ε)

local instance amplificationBidualNormedGroup (X : Type w)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : NormedAddCommGroup (Bidual 𝕜 X) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := StrongDual 𝕜 X) (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

local instance amplificationLiftOperatorNorm : Norm (W →L[𝕜] Bidual 𝕜 Y) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := W) (F := Bidual 𝕜 Y) (σ₁₂ := RingHom.id 𝕜)

/-- A whole-space Lipschitz retraction supplies a bounded uniform approximate
section with error at most `Lε(M+1)`. Genuine quotient lifts are used only
pointwise; the approximate section itself is the regular map `R ∘ S`.
-/
theorem lipschitzRetraction_sphereApproximation
    (Q : Y →L[𝕜] W) (hQ : IsNormQuotient Q)
    (S : W →L[𝕜] Bidual 𝕜 Y) {M ε : ℝ} (_hM : 0 ≤ M) (hε : 0 < ε)
    (hS : ∀ x, ‖S x‖ ≤ M * ‖x‖)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x)
    (K : NNReal) (R : Bidual 𝕜 (AnisotropicSpace Q ε) → AnisotropicSpace Q ε)
    (hR : LipschitzWith K R) (hfix : IsRetraction (bidualEmbedding 𝕜 _) R) :
    ∃ φ : UnitSphere W → Y, UniformContinuous φ ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C) ∧
      (∀ x, ‖Q (φ x) - x.val‖ ≤ (K : ℝ) * ε * (M + 1)) := by
  let T : W →L[𝕜] Bidual 𝕜 (AnisotropicSpace Q ε) :=
    (bidualMap (toAnisotropic Q ε)).comp S
  let φ : UnitSphere W → Y := fun x => fromAnisotropic Q ε (R (T x.val))
  have hR0 : R 0 = 0 := by
    simpa only [(bidualEmbedding 𝕜 (AnisotropicSpace Q ε)).map_zero] using hfix 0
  have hφ : UniformContinuous φ :=
    (fromAnisotropic Q ε).uniformContinuous.comp
      (hR.uniformContinuous.comp (T.uniformContinuous.comp uniformContinuous_subtype_val))
  refine ⟨φ, hφ, ?_, ?_⟩
  · refine ⟨ε⁻¹ * (K : ℝ) * max (ε * M) 1, by positivity, ?_⟩
    intro x
    have hTx : ‖T x.val‖ ≤ max (ε * M) 1 := by
      change ‖bidualMap (toAnisotropic Q ε) (S x.val)‖ ≤ _
      rw [norm_bidual_toAnisotropic Q hε.le, hQS, (bidualEmbedding 𝕜 W).norm_map, x.property]
      apply max_le _ (le_max_right _ _)
      have hs := hS x.val
      rw [x.property, mul_one] at hs
      exact (mul_le_mul_of_nonneg_left hs hε.le).trans (le_max_left _ _)
    have hRx : ‖R (T x.val)‖ ≤ (K : ℝ) * ‖T x.val‖ :=
      hR.norm_le_mul hR0 (T x.val)
    calc
      ‖φ x‖ ≤ ε⁻¹ * ‖R (T x.val)‖ := norm_fromAnisotropic_le Q hε _
      _ ≤ ε⁻¹ * ((K : ℝ) * max (ε * M) 1) :=
        mul_le_mul_of_nonneg_left
          (hRx.trans (mul_le_mul_of_nonneg_left hTx K.coe_nonneg)) (inv_nonneg.mpr hε.le)
      _ = ε⁻¹ * (K : ℝ) * max (ε * M) 1 := (mul_assoc _ _ _).symm
  · intro x
    apply le_of_forall_pos_le_add
    intro d hd
    let c : ℝ := (K : ℝ) * ε
    have hc : 0 ≤ c := mul_nonneg K.coe_nonneg hε.le
    let δ : ℝ := d / (c + 1)
    have hδ : 0 < δ := div_pos hd (by linarith)
    have hδbound : c * δ ≤ d := by
      have heq : δ * (c + 1) = d := div_mul_cancel₀ d (by linarith : c + 1 ≠ 0)
      nlinarith
    obtain ⟨y, hy, hynorm⟩ := hQ.exists_sphere_lift x hδ
    have hker : bidualMap Q (S x.val - bidualEmbedding 𝕜 Y y) = 0 := by
      rw [(bidualMap Q).map_sub, hQS, bidualMap_embedding, hy, sub_self]
    have hnorm : ‖S x.val - bidualEmbedding 𝕜 Y y‖ ≤ M + 1 + δ := by
      have hs := hS x.val
      rw [x.property, mul_one] at hs
      calc
        ‖S x.val - bidualEmbedding 𝕜 Y y‖ ≤ ‖S x.val‖ + ‖bidualEmbedding 𝕜 Y y‖ := norm_sub_le _ _
        _ ≤ M + ‖y‖ := add_le_add hs (le_of_eq ((bidualEmbedding 𝕜 Y).norm_map y))
        _ ≤ M + 1 + δ := by linarith
    have hLip : ‖R (T x.val) - toAnisotropic Q ε y‖ ≤
        (K : ℝ) * (ε * ‖S x.val - bidualEmbedding 𝕜 Y y‖) := by
      have hl := hR.dist_le_mul (T x.val)
        (bidualEmbedding 𝕜 (AnisotropicSpace Q ε) (toAnisotropic Q ε y))
      rw [hfix] at hl
      rw [dist_eq_norm, dist_eq_norm] at hl
      change ‖R (T x.val) - toAnisotropic Q ε y‖ ≤
        (K : ℝ) * ‖bidualMap (toAnisotropic Q ε) (S x.val) -
          bidualEmbedding 𝕜 (AnisotropicSpace Q ε) (toAnisotropic Q ε y)‖ at hl
      rw [← bidualMap_embedding, ← (bidualMap (toAnisotropic Q ε)).map_sub,
        norm_bidual_toAnisotropic_of_ker Q hε.le _ hker] at hl
      exact hl
    calc
      ‖Q (φ x) - x.val‖ =
          ‖anisotropicQuotient Q ε (R (T x.val) - toAnisotropic Q ε y)‖ := by
        change ‖Q (fromAnisotropic Q ε (R (T x.val))) - x.val‖ = _
        rw [quotient_fromAnisotropic Q hε, map_sub,
          anisotropicQuotient_toAnisotropic, hy]
      _ ≤ ‖R (T x.val) - toAnisotropic Q ε y‖ := anisotropicQuotient_norm_le Q ε _
      _ ≤ (K : ℝ) * (ε * ‖S x.val - bidualEmbedding 𝕜 Y y‖) := hLip
      _ ≤ c * (M + 1 + δ) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hnorm hc
      _ ≤ (K : ℝ) * ε * (M + 1) + d := by
        change c * (M + 1 + δ) ≤ c * (M + 1) + d
        nlinarith

/-- A stronger version of the lower bound in `thm:amplification`: positivity
of `ε` suffices for the quantitative conclusion. -/
theorem amplification_lipschitz_constant_lower [CompleteSpace Y] [CompleteSpace W]
    (Q : Y →L[𝕜] W) (hQ : IsNormQuotient Q) (hNoSection : ¬ HasUniformSectionOnUnitBall Q)
    (S : W →L[𝕜] Bidual 𝕜 Y) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hS : ∀ x, ‖S x‖ ≤ M * ‖x‖)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x)
    (K : NNReal) (R : Bidual 𝕜 (AnisotropicSpace Q ε) → AnisotropicSpace Q ε)
    (hR : LipschitzWith K R) (hfix : IsRetraction (bidualEmbedding 𝕜 _) R) :
    1 / (ε * (M + 1)) ≤ (K : ℝ) := by
  have hLower : 1 ≤ (K : ℝ) * ε * (M + 1) := by
    by_contra! hlt
    obtain ⟨φ, hφ, hbound, herror⟩ := lipschitzRetraction_sphereApproximation
      Q hQ S hM hε hS hQS K R hR hfix
    apply hNoSection
    exact correction (E := Y) (W := W) Q hQ φ hφ hbound
      ((K : ℝ) * ε * (M + 1)) (by positivity) hlt herror
  apply (div_le_iff₀ (mul_pos hε (by linarith : 0 < M + 1))).mpr
  nlinarith


end LindenstraussRetraction

