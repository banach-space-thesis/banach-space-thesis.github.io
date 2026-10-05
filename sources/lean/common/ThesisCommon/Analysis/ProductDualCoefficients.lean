import ThesisCommon.Analysis.ProductDualNorm
import ThesisCommon.Analysis.LpOnePair

/-! Isometric atomic models of the two coordinate duals give an isometric
atomic model of the full max-norm product dual, including surjectivity. -/
noncomputable section
namespace ThesisCommon
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dualProdLpIsometry (e : (E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : I => ℝ) 1)
    (f : (F →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : I => ℝ) 1) :
    ((E × F) →L[ℝ] ℝ) →ₗᵢ[ℝ] lp (fun _ : Bool × I => ℝ) 1 where
  toFun φ := lpOnePair (e (dualProdLeft φ)) (f (dualProdRight φ))
  map_add' φ ψ := by
    apply lp.ext
    funext ⟨side,i⟩
    cases side <;> simp [dualProdLeft,dualProdRight,ContinuousLinearMap.add_comp]
  map_smul' r φ := by
    apply lp.ext
    funext ⟨side,i⟩
    cases side <;> simp [dualProdLeft,dualProdRight,ContinuousLinearMap.smul_comp]
  norm_map' φ := by
    change ‖lpOnePair (e (dualProdLeft φ)) (f (dualProdRight φ))‖ = ‖φ‖
    rw [lpOnePair_norm,e.norm_map,f.norm_map,← dualProd_norm]

theorem dualProdLpIsometry_surjective (e : (E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : I => ℝ) 1)
    (f : (F →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : I => ℝ) 1) :
    Function.Surjective (dualProdLpIsometry e f) := by
  intro c
  let L : I ↪ Bool × I := ⟨fun i => (false,i),by intro i j h; exact congrArg Prod.snd h⟩
  let R : I ↪ Bool × I := ⟨fun i => (true,i),by intro i j h; exact congrArg Prod.snd h⟩
  let φ := e.symm (lpOneComap L c)
  let ψ := f.symm (lpOneComap R c)
  let θ : (E × F) →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.fst ℝ E F) +
    ψ.comp (ContinuousLinearMap.snd ℝ E F)
  have hL : dualProdLeft θ = φ := by ext x; simp [θ,dualProdLeft]
  have hR : dualProdRight θ = ψ := by ext y; simp [θ,dualProdRight]
  refine ⟨θ,?_⟩
  apply lp.ext
  funext ⟨side,i⟩
  cases side
  · change e (dualProdLeft θ) i = c (false,i)
    rw [hL]
    exact congrArg (fun d : lp (fun _ : I => ℝ) 1 => d i) (e.apply_symm_apply _)
  · change f (dualProdRight θ) i = c (true,i)
    rw [hR]
    exact congrArg (fun d : lp (fun _ : I => ℝ) 1 => d i) (f.apply_symm_apply _)

def dualProdLpEquiv (e : (E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : I => ℝ) 1)
    (f : (F →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : I => ℝ) 1) :
    ((E × F) →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : Bool × I => ℝ) 1 :=
  LinearIsometryEquiv.ofSurjective (dualProdLpIsometry e f) (dualProdLpIsometry_surjective e f)

end ThesisCommon
