import LindenstraussRetraction.AmplificationCore
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

local instance amplificationWrapperAnisotropicNormedSpace (Q : Y →L[𝕜] W) (ε : ℝ) :
    NormedSpace 𝕜 (AnisotropicSpace Q ε) :=
  Submodule.normedSpace (𝕜 := 𝕜) (R := 𝕜) (E := Y × W) (AnisotropicSpace Q ε)

local instance amplificationWrapperBidualNormedGroup (X : Type w)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : NormedAddCommGroup (Bidual 𝕜 X) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := StrongDual 𝕜 X) (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

local instance amplificationWrapperBidualNormedSpace (X : Type w)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : NormedSpace 𝕜 (Bidual 𝕜 X) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := 𝕜) (𝕜₂ := 𝕜) (𝕜' := 𝕜)
    (E := StrongDual 𝕜 X) (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

local instance amplificationWrapperLiftOperatorNorm : Norm (W →L[𝕜] Bidual 𝕜 Y) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := W) (F := Bidual 𝕜 Y) (σ₁₂ := RingHom.id 𝕜)

/-- The infimum over all admissible Lipschitz bounds satisfies the paper's
amplification estimate, including the case in which no retraction exists. -/
theorem amplification [CompleteSpace Y] [CompleteSpace W]
    (Q : Y →L[𝕜] W) (hQ : IsNormQuotient Q) (hNoSection : ¬ HasUniformSectionOnUnitBall Q)
    (S : W →L[𝕜] Bidual 𝕜 Y) {ε : ℝ} (hε : 0 < ε)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x) :
    ENNReal.ofReal (1 / (ε * (‖S‖ + 1))) ≤
      bidualLipschitzRetractionConstant 𝕜 (AnisotropicSpace Q ε) := by
  have hSnorm : 0 ≤ ‖S‖ := S.opNorm_nonneg
  have hSbound : ∀ x : W, ‖S x‖ ≤ ‖S‖ * ‖x‖ := fun x => S.le_opNorm x
  apply le_sInf
  rintro L ⟨K, R, rfl, hR, hfix⟩
  have h := amplification_lipschitz_constant_lower Q hQ hNoSection S (M := ‖S‖)
    hSnorm hε hSbound hQS K R hR hfix
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal h

end LindenstraussRetraction

