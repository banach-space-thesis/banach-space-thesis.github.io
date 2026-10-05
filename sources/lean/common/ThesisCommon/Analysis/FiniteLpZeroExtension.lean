import ThesisCommon.Analysis.LpOperators
import Mathlib.Analysis.Normed.Lp.LpEquiv

/-! Contractive zero extension of finite lp vectors along an actual index
embedding, using the established isometry between finite lp and PiLp. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent)
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finiteLpExtend (e : ι ↪ κ) :
    PiLp p.val (fun _ : ι => 𝕜) →L[𝕜] PiLp p.val (fun _ : κ => 𝕜) :=
  (lpPiLpₗᵢ (fun _ : κ => 𝕜) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lpExtend p.val e).comp
      (lpPiLpₗᵢ (fun _ : ι => 𝕜) 𝕜).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem finiteLpExtend_apply (e : ι ↪ κ) (x : PiLp p.val (fun _ : ι => 𝕜)) (j : κ) :
    finiteLpExtend p e x j = Function.extend e x 0 j := rfl

@[simp] theorem finiteLpExtend_apply_image (e : ι ↪ κ)
    (x : PiLp p.val (fun _ : ι => 𝕜)) (i : ι) : finiteLpExtend p e x (e i) = x i :=
  e.injective.extend_apply x 0 i

theorem finiteLpExtend_apply_off_range (e : ι ↪ κ)
    (x : PiLp p.val (fun _ : ι => 𝕜)) {j : κ} (hj : j ∉ Set.range e) :
    finiteLpExtend p e x j = 0 := by
  rw [finiteLpExtend_apply]
  exact Function.extend_apply' (f := e) x 0 j hj

theorem finiteLpExtend_norm_le (e : ι ↪ κ) (x : PiLp p.val (fun _ : ι => 𝕜)) :
    ‖finiteLpExtend p e x‖ ≤ ‖x‖ := by
  change ‖lpPiLpₗᵢ (fun _ : κ => 𝕜) 𝕜
    (lpExtend (𝕜 := 𝕜) (X := 𝕜) p.val e
      ((lpPiLpₗᵢ (fun _ : ι => 𝕜) 𝕜).symm x))‖ ≤ ‖x‖
  rw [LinearIsometryEquiv.norm_map]
  exact ((lpExtend (𝕜 := 𝕜) (X := 𝕜) p.val e).le_of_opNorm_le
    (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) e) _).trans_eq
    (by simp)

end ThesisCommon
