import LindenstraussRetraction.Renorming
import LindenstraussRetraction.BidualProduct

/-! # The exact continuous-bidual norm of the anisotropic renorming -/

noncomputable section

namespace LindenstraussRetraction

universe u v w s

variable {𝕜 : Type s} [RCLike 𝕜]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

local instance anisotropicNormedSpace (Q : Y →L[𝕜] W) (ε : ℝ) :
    NormedSpace 𝕜 (AnisotropicSpace Q ε) :=
  Submodule.normedSpace (𝕜 := 𝕜) (R := 𝕜) (E := Y × W) (AnisotropicSpace Q ε)

local instance bidualNormedSpace (X : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    NormedSpace 𝕜 (Bidual 𝕜 X) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := 𝕜) (𝕜₂ := 𝕜) (𝕜' := 𝕜)
    (E := StrongDual 𝕜 X) (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

@[simp] theorem transpose_smul_apply (c : 𝕜) (Q : Y →L[𝕜] W) (f : StrongDual 𝕜 W) :
    transpose (c • Q) f = c • transpose Q f := by
  ext y
  simp [transpose_apply]

@[simp] theorem bidualMap_smul (c : 𝕜) (Q : Y →L[𝕜] W) :
    bidualMap (c • Q) = c • bidualMap Q := by
  ext z f
  simp [bidualMap_apply]

@[simp] theorem fst_anisotropic_comp (Q : Y →L[𝕜] W) (ε : ℝ) :
    (ContinuousLinearMap.fst 𝕜 Y W).comp
      ((anisotropicInclusion Q ε).toContinuousLinearMap.comp (toAnisotropic Q ε)) =
      (ε : 𝕜) • ContinuousLinearMap.id 𝕜 Y := by
  ext y
  rfl

@[simp] theorem snd_anisotropic_comp (Q : Y →L[𝕜] W) (ε : ℝ) :
    (ContinuousLinearMap.snd 𝕜 Y W).comp
      ((anisotropicInclusion Q ε).toContinuousLinearMap.comp (toAnisotropic Q ε)) = Q := by
  ext y
  rfl

/-- Proposition `prop:bidual-norm` of the paper, expressed via the explicit
continuous linear correspondence with the renormed model. -/
theorem norm_bidual_toAnisotropic (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 ≤ ε)
    (z : Bidual 𝕜 Y) :
    ‖bidualMap (toAnisotropic Q ε) z‖ = max (ε * ‖z‖) ‖bidualMap Q z‖ := by
  let I := anisotropicInclusion Q ε
  let T := I.toContinuousLinearMap.comp (toAnisotropic Q ε)
  have hf : bidualMap (ContinuousLinearMap.fst 𝕜 Y W) (bidualMap T z) = (ε : 𝕜) • z := by
    change ((bidualMap (ContinuousLinearMap.fst 𝕜 Y W)).comp (bidualMap T)) z = _
    rw [← bidualMap_comp, fst_anisotropic_comp, bidualMap_smul, bidualMap_id]
    rfl
  have hg : bidualMap (ContinuousLinearMap.snd 𝕜 Y W) (bidualMap T z) = bidualMap Q z := by
    change ((bidualMap (ContinuousLinearMap.snd 𝕜 Y W)).comp (bidualMap T)) z = _
    rw [← bidualMap_comp, snd_anisotropic_comp]
  calc
    ‖bidualMap (toAnisotropic Q ε) z‖ =
        ‖bidualMap I.toContinuousLinearMap (bidualMap (toAnisotropic Q ε) z)‖ :=
      (norm_bidualMap_isometry I _).symm
    _ = ‖bidualMap T z‖ := by rw [bidualMap_comp]; rfl
    _ = max ‖bidualMap (ContinuousLinearMap.fst 𝕜 Y W) (bidualMap T z)‖
        ‖bidualMap (ContinuousLinearMap.snd 𝕜 Y W) (bidualMap T z)‖ :=
      norm_bidual_product _
    _ = max (ε * ‖z‖) ‖bidualMap Q z‖ := by
      haveI : NormSMulClass 𝕜 (Bidual 𝕜 Y) :=
        NormedSpace.toNormSMulClass (𝕜 := 𝕜) (E := Bidual 𝕜 Y)
      rw [hf, hg, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hε]

/-- On the kernel of the second adjoint of `Q`, the bidual renorming is exactly
the scalar multiple `ε` of the original bidual norm. This is the estimate used
to compare bidual lifts and genuine lifts in the main construction. -/
theorem norm_bidual_toAnisotropic_of_ker (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 ≤ ε)
    (z : Bidual 𝕜 Y) (hz : bidualMap Q z = 0) :
    ‖bidualMap (toAnisotropic Q ε) z‖ = ε * ‖z‖ := by
  rw [norm_bidual_toAnisotropic Q hε, hz]
  rw [show ‖(0 : Bidual 𝕜 W)‖ = 0 from ContinuousLinearMap.opNorm_zero]
  exact max_eq_left (mul_nonneg hε (norm_nonneg z))

end LindenstraussRetraction
