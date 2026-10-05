import ThesisCommon.Analysis.SigmaComplexProductDualNorm
import ThesisCommon.Analysis.SigmaComplexLpOneComap

/-! Isometric atomic models of the two coordinate duals give an isometric
atomic model of the full max-norm product dual, including surjectivity. -/
noncomputable section
namespace ThesisCommon
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def complexDualProdLpIsometry (e : (E →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : I => ℂ) 1)
    (f : (F →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : I => ℂ) 1) :
    ((E × F) →L[ℂ] ℂ) →ₗᵢ[ℂ] lp (fun _ : Bool × I => ℂ) 1 where
  toFun φ := complexLpOnePair (e (complexDualProdLeft φ)) (f (complexDualProdRight φ))
  map_add' φ ψ := by
    apply lp.ext
    funext ⟨side,i⟩
    cases side <;> simp [complexDualProdLeft,complexDualProdRight,ContinuousLinearMap.add_comp]
  map_smul' r φ := by
    apply lp.ext
    funext ⟨side,i⟩
    cases side <;> simp [complexDualProdLeft,complexDualProdRight,ContinuousLinearMap.smul_comp]
  norm_map' φ := by
    change ‖complexLpOnePair (e (complexDualProdLeft φ)) (f (complexDualProdRight φ))‖ = ‖φ‖
    rw [complexLpOnePair_norm,e.norm_map,f.norm_map,← complexDualProd_norm]

theorem complexDualProdLpIsometry_surjective (e : (E →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : I => ℂ) 1)
    (f : (F →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : I => ℂ) 1) :
    Function.Surjective (complexDualProdLpIsometry e f) := by
  intro c
  let L : I ↪ Bool × I := ⟨fun i => (false,i),by intro i j h; exact congrArg Prod.snd h⟩
  let R : I ↪ Bool × I := ⟨fun i => (true,i),by intro i j h; exact congrArg Prod.snd h⟩
  let φ := e.symm (complexLpOneComap L c)
  let ψ := f.symm (complexLpOneComap R c)
  let θ : (E × F) →L[ℂ] ℂ := φ.comp (ContinuousLinearMap.fst ℂ E F) +
    ψ.comp (ContinuousLinearMap.snd ℂ E F)
  have hL : complexDualProdLeft θ = φ := by ext x; simp [θ,complexDualProdLeft]
  have hR : complexDualProdRight θ = ψ := by ext y; simp [θ,complexDualProdRight]
  refine ⟨θ,?_⟩
  apply lp.ext
  funext ⟨side,i⟩
  cases side
  · change e (complexDualProdLeft θ) i = c (false,i)
    rw [hL]
    exact congrArg (fun d : lp (fun _ : I => ℂ) 1 => d i) (e.apply_symm_apply _)
  · change f (complexDualProdRight θ) i = c (true,i)
    rw [hR]
    exact congrArg (fun d : lp (fun _ : I => ℂ) 1 => d i) (f.apply_symm_apply _)

def complexDualProdLpEquiv (e : (E →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : I => ℂ) 1)
    (f : (F →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : I => ℂ) 1) :
    ((E × F) →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : Bool × I => ℂ) 1 :=
  LinearIsometryEquiv.ofSurjective (complexDualProdLpIsometry e f) (complexDualProdLpIsometry_surjective e f)

end ThesisCommon


