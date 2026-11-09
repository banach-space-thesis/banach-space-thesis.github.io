import BanachIsometric.SignedConeSourceChart
import BanachIsometric.SignedRayTransportDerivative

/-! A coned-simplex chart followed by a positive normalization of its
radius has determinant sign equal to the ordered target vertex matrix. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Filter Matrix
open scoped Topology

theorem differentiableAt_radialFactor_of_signedConeMatrix_germ (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hM : M.det ≠ 0)
    {a : (Fin n → ℝ) → ℝ} {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} {u : Fin (n + 1) → ℝ}
    (hr : 0 < u 0) (hF : DifferentiableAt ℝ F (signedConeSourceChart n u))
    (he : ∀ᶠ z in 𝓝 u, F (signedConeSourceChart n z) =
      M.mulVec (signedConeSourceChart n (signedRayTransport n a id z))) :
    DifferentiableAt ℝ a (signedTailLinear n u) := by
  let x₀ := signedTailLinear n u
  let D : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi (Fin.cons 0 (fun j => ContinuousLinearMap.proj j))
  let b : Fin (n + 1) → ℝ := Fin.cons (u 0) 0
  let U : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun x => b + D x
  have hU (x : Fin n → ℝ) : U x = Fin.cons (u 0) x := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change u 0 + 0 = u 0
      exact add_zero _
    · change 0 + x k = x k
      exact zero_add _
  have hu : U x₀ = u := by
    rw [hU]
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
  have hdU : DifferentiableAt ℝ U x₀ := (differentiableAt_const b).add D.differentiableAt
  have htU : Tendsto U (𝓝 x₀) (𝓝 u) := by
    rw [← hu]
    exact hdU.continuousAt.tendsto
  let E := ((Matrix.toLin' M).equivOfDetNeZero (by rwa [LinearMap.det_toLin'])).toContinuousLinearEquiv
  let mass := (signedSimplexCoordinateSum (n + 1)).toContinuousLinearMap
  let G : (Fin n → ℝ) → ℝ := fun x => (u 0)⁻¹ * mass (E.symm (F (signedConeSourceChart n (U x))))
  have hS : DifferentiableAt ℝ (signedConeSourceChart n) (U x₀) :=
    (signedConeSourceChart_hasStrictFDerivAt n (U x₀)).hasFDerivAt.differentiableAt
  have hF' : DifferentiableAt ℝ F (signedConeSourceChart n (U x₀)) := by rwa [hu]
  have hG : DifferentiableAt ℝ G x₀ := (differentiableAt_const ((u 0)⁻¹)).mul
    (mass.differentiableAt.comp x₀ (E.symm.differentiableAt.comp x₀ (hF'.comp x₀ (hS.comp x₀ hdU))))
  apply hG.congr_of_eventuallyEq
  filter_upwards [htU.eventually he] with x hx
  change a x = (u 0)⁻¹ * mass (E.symm (F (signedConeSourceChart n (U x))))
  rw [hx]
  change a x = (u 0)⁻¹ * mass (E.symm (E (signedConeSourceChart n (signedRayTransport n a id (U x)))))
  rw [E.symm_apply_apply, signedConeSourceChart_apply, map_smul]
  have hhead : signedRayTransport n a id (U x) 0 = U x 0 * a (signedTailLinear n (U x)) := rfl
  have htail : signedTailLinear n (signedRayTransport n a id (U x)) = signedTailLinear n (U x) := by
    funext j
    change (Fin.cons (α := fun _ : Fin (n + 1) => ℝ)
      (U x 0 * a (signedTailLinear n (U x))) (signedTailLinear n (U x))) j.succ = _
    rfl
  have hmass (y : Fin (n + 1) → ℝ) : mass y = ∑ j, y j := signedSimplexCoordinateSum_apply (n + 1) y
  rw [hhead, htail, hmass, smul_eq_mul, signedSimplexBarycentric_sum, mul_one, hU]
  change a x = (u 0)⁻¹ * (u 0 * a x)
  rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

theorem det_fderiv_of_signedConeMatrix_germ (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {a : (Fin n → ℝ) → ℝ} {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} {u : Fin (n + 1) → ℝ}
    (hr : 0 < u 0) (ha : DifferentiableAt ℝ a (signedTailLinear n u))
    (he : ∀ᶠ z in 𝓝 u, F (signedConeSourceChart n z) =
      M.mulVec (signedConeSourceChart n (signedRayTransport n a id z))) :
    DifferentiableAt ℝ F (signedConeSourceChart n u) ∧
      (fderiv ℝ F (signedConeSourceChart n u)).det = M.det * a (signedTailLinear n u) ^ (n + 1) := by
  let A := (signedConeHeadAdjustment n).comp (signedTargetRayDerivative n u)
  have hA : A.det = (u 0) ^ n := signedConeSourceChart_derivative_det n u
  have hAne : A.det ≠ 0 := by rw [hA]; exact (pow_pos hr _).ne'
  let e := (A.toLinearMap.equivOfDetNeZero hAne).toContinuousLinearEquiv
  have heA : (e : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) = A := by
    ext z j
    rfl
  have hS : HasStrictFDerivAt (signedConeSourceChart n)
      (e : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) u := by
    rw [heA]
    exact signedConeSourceChart_hasStrictFDerivAt n u
  let L := signedRayTransport n a id
  obtain ⟨D, hD, hd⟩ := signedRayTransport_hasFDerivAt n ha.hasFDerivAt
    (hasFDerivAt_id (signedTailLinear n u))
  have hDdet : D.det = a (signedTailLinear n u) := by
    rw [hd]
    change a (signedTailLinear n u) * (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)).det = _
    rw [LinearMap.det_id, mul_one]
  let B₀ := (signedConeHeadAdjustment n).comp (signedTargetRayDerivative n (L u))
  let B := (Matrix.toLin' M).toContinuousLinearMap.comp B₀
  have hB : HasFDerivAt (fun z => M.mulVec (signedConeSourceChart n z)) B (L u) :=
    (Matrix.toLin' M).toContinuousLinearMap.hasFDerivAt.comp (L u)
      (signedConeSourceChart_hasStrictFDerivAt n (L u)).hasFDerivAt
  have hBdet : B.det = M.det * ((u 0) * a (signedTailLinear n u)) ^ n := by
    change (LinearMap.comp (Matrix.toLin' M) B₀.toLinearMap).det = _
    rw [LinearMap.det_comp, LinearMap.det_toLin']
    change M.det * B₀.det = _
    have hB₀ : B₀.det = ((u 0) * a (signedTailLinear n u)) ^ n :=
      signedConeSourceChart_derivative_det n (L u)
    rw [hB₀]
  refine ⟨(hasFDerivAt_of_chart_semiconjugacy hS hB hD he).differentiableAt, ?_⟩
  rw [det_fderiv_eq_of_chart_semiconjugacy hS hB hD he, heA, hA, hBdet, hDdet, mul_pow]
  calc
    _ = (M.det * a (signedTailLinear n u) ^ (n + 1)) * ((u 0) ^ n * ((u 0) ^ n)⁻¹) := by
      rw [pow_succ]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero n hr.ne'), mul_one]

end BanachIsometric.SingularPrism
