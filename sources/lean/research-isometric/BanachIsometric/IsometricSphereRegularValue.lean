import BanachIsometric.SphereDegreeIsometricCoordinates

/-! Actual regular cone values under genuine linear isometric sphere
coordinates. The same isometry conjugates source and target, so the actual
derivative determinant is unchanged. Fibers in the unchanged closed unit
balls correspond without a finiteness or regularity premise. -/

noncomputable section
namespace BanachIsometric
open Set Metric

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem unitSphereCone_isometricSphereConjugate_eq_coordinate
    (L : W ≃ₗᵢ[ℝ] V) (f : sphere (0 : V) 1 → sphere (0 : V) 1) :
    unitSphereCone (isometricSphereConjugate L f) =
      coordinateMapConjugate L.symm.toContinuousLinearEquiv (unitSphereCone f) := by
  funext x
  exact unitSphereCone_isometricSphereConjugate L f x

theorem det_fderiv_unitSphereCone_isometricSphereConjugate
    (L : W ≃ₗᵢ[ℝ] V) (f : sphere (0 : V) 1 → sphere (0 : V) 1) (x : W) :
    (fderiv ℝ (unitSphereCone (isometricSphereConjugate L f)) x).det =
      (fderiv ℝ (unitSphereCone f) (L x)).det := by
  rw [unitSphereCone_isometricSphereConjugate_eq_coordinate]
  have h := det_fderiv_coordinateConjugate L.symm.toContinuousLinearEquiv
    (unitSphereCone f) (L x)
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] using h

theorem differentiableAt_unitSphereCone_isometricSphereConjugate
    (L : W ≃ₗᵢ[ℝ] V) (f : sphere (0 : V) 1 → sphere (0 : V) 1) (x : W)
    (hx : DifferentiableAt ℝ (unitSphereCone f) (L x)) :
    DifferentiableAt ℝ (unitSphereCone (isometricSphereConjugate L f)) x := by
  rw [unitSphereCone_isometricSphereConjugate_eq_coordinate]
  exact L.symm.toContinuousLinearEquiv.differentiableAt.comp x
    (hx.comp x L.toContinuousLinearEquiv.differentiableAt)

theorem isometricSphereCone_fiber_image (L : W ≃ₗᵢ[ℝ] V)
    (f : sphere (0 : V) 1 → sphere (0 : V) 1) (y : V) {x : W}
    (hx : unitSphereCone (isometricSphereConjugate L f) x = L.symm y) :
    unitSphereCone f (L x) = y := by
  rw [unitSphereCone_isometricSphereConjugate] at hx
  exact L.symm.injective hx

def isometricSphereConeBallFiberEquiv (L : W ≃ₗᵢ[ℝ] V)
    (f : sphere (0 : V) 1 → sphere (0 : V) 1) (y : V) :
    {x : W // x ∈ closedBall 0 1 ∧
      unitSphereCone (isometricSphereConjugate L f) x = L.symm y} ≃
      {z : V // z ∈ closedBall 0 1 ∧ unitSphereCone f z = y} where
  toFun x := ⟨L x.val, by
    constructor
    · simpa only [mem_closedBall, dist_zero_right, L.norm_map] using x.property.1
    · exact isometricSphereCone_fiber_image L f y x.property.2⟩
  invFun z := ⟨L.symm z.val, by
    constructor
    · simpa only [mem_closedBall, dist_zero_right, L.symm.norm_map] using z.property.1
    · rw [unitSphereCone_isometricSphereConjugate, L.apply_symm_apply, z.property.2]⟩
  left_inv x := Subtype.ext (L.symm_apply_apply x.val)
  right_inv z := Subtype.ext (L.apply_symm_apply z.val)

theorem card_isometricSphereConeBallFiber (L : W ≃ₗᵢ[ℝ] V)
    (f : sphere (0 : V) 1 → sphere (0 : V) 1) (y : V) :
    Nat.card {x : W // x ∈ closedBall 0 1 ∧
      unitSphereCone (isometricSphereConjugate L f) x = L.symm y} =
      Nat.card {z : V // z ∈ closedBall 0 1 ∧ unitSphereCone f z = y} :=
  Nat.card_congr (isometricSphereConeBallFiberEquiv L f y)

theorem positive_regular_anchor_isometricSphereConjugate
    (L : W ≃ₗᵢ[ℝ] V) (f : sphere (0 : V) 1 → sphere (0 : V) 1) (y : V)
    (hdiff : ∀ z ∈ closedBall (0 : V) 1, unitSphereCone f z = y →
      DifferentiableAt ℝ (unitSphereCone f) z)
    (hpos : ∀ z ∈ closedBall (0 : V) 1, unitSphereCone f z = y →
      0 < (fderiv ℝ (unitSphereCone f) z).det) :
    ∀ x ∈ closedBall (0 : W) 1,
      unitSphereCone (isometricSphereConjugate L f) x = L.symm y →
        DifferentiableAt ℝ (unitSphereCone (isometricSphereConjugate L f)) x ∧
          0 < (fderiv ℝ (unitSphereCone (isometricSphereConjugate L f)) x).det := by
  intro x hx hxy
  have hb : L x ∈ closedBall (0 : V) 1 := by
    simpa only [mem_closedBall, dist_zero_right, L.norm_map] using hx
  have hpre := isometricSphereCone_fiber_image L f y hxy
  refine ⟨differentiableAt_unitSphereCone_isometricSphereConjugate L f x
    (hdiff _ hb hpre), ?_⟩
  rw [det_fderiv_unitSphereCone_isometricSphereConjugate]
  exact hpos _ hb hpre

end BanachIsometric
