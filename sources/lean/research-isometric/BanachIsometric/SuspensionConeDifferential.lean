import BanachIsometric.SuspensionConeProduct

/-! The actual cone product formula gives Lipschitz regularity of the
suspension and equality of its Jacobian determinant with the equatorial one.
The coordinate equivalence is continuous linear with the original norms. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem coordinateConjugate_unitSphereCone_of_band
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z)) :
    coordinateMapConjugate (equatorSplit v) (unitSphereCone φ) =
      Prod.map id (unitSphereCone f) := by
  funext p
  change equatorSplit v (unitSphereCone φ ((equatorSplit v).symm p)) = _
  rw [equatorSplit_symm_apply, unitSphereCone_band_product v q₀ f φ hBand]
  change equatorSplit v ((equatorSplit v).symm (p.1, unitSphereCone f p.2)) = _
  exact (equatorSplit v).apply_symm_apply _

theorem exists_lipschitz_unitSphereCone_of_band
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    {C : ℝ≥0} (hf : LipschitzWith C f) :
    ∃ L : ℝ≥0, LipschitzWith L (unitSphereCone φ) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_unitSphereCone hf
  have hP : LipschitzWith (max 1 L)
      (Prod.map id (unitSphereCone f) : ℝ × (ℝ ∙ v.val)ᗮ → ℝ × (ℝ ∙ v.val)ᗮ) :=
    by simpa only [mul_one] using
      (LipschitzWith.prod_fst).prodMk (hL.comp LipschitzWith.prod_snd)
  let e := equatorSplit v
  have h := e.symm.lipschitz.comp (hP.comp e.lipschitz)
  have heq : unitSphereCone φ = e.symm ∘ Prod.map id (unitSphereCone f) ∘ e := by
    funext x
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, e.apply_symm_apply]
    simpa only [coordinateMapConjugate, e, ContinuousLinearEquiv.symm_apply_apply] using
      congrFun (coordinateConjugate_unitSphereCone_of_band v q₀ f φ hBand) (e x)
  refine ⟨‖(e.symm : (ℝ × (ℝ ∙ v.val)ᗮ) →L[ℝ] V)‖₊ *
    (max 1 L * ‖(e : V →L[ℝ] (ℝ × (ℝ ∙ v.val)ᗮ))‖₊), ?_⟩
  rw [heq]
  exact h

theorem exists_lipschitz_sphereMap_of_band
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    {C : ℝ≥0} (hf : LipschitzWith C f) :
    ∃ L : ℝ≥0, LipschitzWith L φ := by
  obtain ⟨L, hL⟩ := exists_lipschitz_unitSphereCone_of_band v q₀ f φ hBand hf
  refine ⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have h := (hL.comp (LipschitzWith.subtype_val _)).dist_le_mul x y
  simpa only [Function.comp_apply, mul_one, unitSphereCone, coneExtension_unit,
    Subtype.dist_eq] using h

theorem differentiableAt_unitSphereCone_of_band
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    (a : ℝ) (w : (ℝ ∙ v.val)ᗮ)
    (hw : DifferentiableAt ℝ (unitSphereCone f) w) :
    DifferentiableAt ℝ (unitSphereCone φ) (a • v.val + (w : V)) := by
  let e := equatorSplit v
  have hP : DifferentiableAt ℝ (Prod.map id (unitSphereCone f)) (a, w) :=
    DifferentiableAt.prodMap (a, w) differentiableAt_id hw
  have hC : DifferentiableAt ℝ (coordinateMapConjugate e (unitSphereCone φ)) (a, w) := by
    rw [coordinateConjugate_unitSphereCone_of_band v q₀ f φ hBand]
    exact hP
  have hSC : DifferentiableAt ℝ (e.symm ∘ coordinateMapConjugate e (unitSphereCone φ))
      (e (e.symm (a, w))) := by
    rw [e.apply_symm_apply]
    exact e.symm.differentiableAt.comp (a, w) hC
  have h := hSC.comp (e.symm (a, w)) e.differentiableAt
  have hh : DifferentiableAt ℝ (unitSphereCone φ) (e.symm (a, w)) := by
    simpa only [coordinateMapConjugate, Function.comp_def, e.symm_apply_apply] using h
  exact hh

theorem det_fderiv_unitSphereCone_of_band
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    (a : ℝ) (w : (ℝ ∙ v.val)ᗮ)
    (hw : DifferentiableAt ℝ (unitSphereCone f) w) :
    (fderiv ℝ (unitSphereCone φ) (a • v.val + (w : V))).det =
      (fderiv ℝ (unitSphereCone f) w).det := by
  let e := equatorSplit v
  have hP : HasFDerivAt (Prod.map id (unitSphereCone f))
      ((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ (unitSphereCone f) w)) (a, w) :=
    HasFDerivAt.prodMap (a, w) (hasFDerivAt_id a) hw.hasFDerivAt
  have hC : HasFDerivAt (coordinateMapConjugate e (unitSphereCone φ))
      ((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ (unitSphereCone f) w)) (a, w) := by
    rw [coordinateConjugate_unitSphereCone_of_band v q₀ f φ hBand]
    exact hP
  have hd := det_fderiv_coordinateConjugate e (unitSphereCone φ) (e.symm (a, w))
  rw [e.apply_symm_apply, hC.fderiv] at hd
  have hp : ((ContinuousLinearMap.id ℝ ℝ).prodMap
      (fderiv ℝ (unitSphereCone f) w)).det = (fderiv ℝ (unitSphereCone f) w).det := by
    change ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
      (fderiv ℝ (unitSphereCone f) w).toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  rw [hp] at hd
  exact hd.symm

end BanachIsometric
