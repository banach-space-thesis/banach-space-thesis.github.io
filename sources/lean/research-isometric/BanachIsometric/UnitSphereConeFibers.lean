import BanachIsometric.SphereConeCount
import BanachIsometric.ConeGeometry

/-! # Actual cone fibers are the actual sphere fibers at the normalized target -/

namespace BanachIsometric

open Set Metric NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem normalize_unitSphereCone (φ : sphere (0 : V) 1 → sphere (0 : V) 1)
    (x : V) (hx : x ≠ 0) :
    normalize (unitSphereCone φ x) = (φ (coneDirection x hx)).val := by
  rw [unitSphereCone, coneExtension_of_ne _ x hx, normalize_smul_of_pos (norm_pos_iff.mpr hx)]
  apply normalize_eq_self_of_norm_eq_one
  simpa only [mem_sphere, dist_zero_right] using (φ (coneDirection x hx)).property

theorem unitSphereCone_preimage_ne_zero (φ : sphere (0 : V) 1 → sphere (0 : V) 1)
    {y x : V} (hy : y ≠ 0) (hxy : unitSphereCone φ x = y) : x ≠ 0 := by
  intro hx
  exact hy (hxy.symm.trans ((unitSphereCone_eq_zero_iff φ x).mpr hx))

noncomputable def unitSphereConeFiberEquiv
    (φ : sphere (0 : V) 1 → sphere (0 : V) 1) (y : V) (hy : y ≠ 0) (hyball : ‖y‖ ≤ 1) :
    {x : V // x ∈ closedBall (0 : V) 1 ∧ unitSphereCone φ x = y} ≃
      {u : sphere (0 : V) 1 // φ u = coneDirection y hy} where
  toFun x := ⟨coneDirection x.val (unitSphereCone_preimage_ne_zero φ hy x.property.2), by
    apply Subtype.ext
    have h := congrArg NormedSpace.normalize x.property.2
    rw [normalize_unitSphereCone φ x.val (unitSphereCone_preimage_ne_zero φ hy x.property.2)] at h
    exact h⟩
  invFun u := ⟨‖y‖ • u.val.val, by
    have hu : ‖u.val.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using u.val.property
    constructor
    · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (norm_nonneg _), hu, mul_one]
      exact hyball
    · change coneExtension (fun v => (φ v).val) (‖y‖ • u.val.val) = y
      rw [coneExtension_smul_nonneg _ (norm_nonneg _), coneExtension_unit, u.property]
      exact norm_smul_normalize y⟩
  left_inv x := by
    apply Subtype.ext
    change ‖y‖ • normalize x.val = x.val
    have hnorm : ‖x.val‖ = ‖y‖ := by rw [← norm_unitSphereCone φ x.val, x.property.2]
    rw [← hnorm]
    exact norm_smul_normalize x.val
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change normalize (‖y‖ • u.val.val) = u.val.val
    rw [normalize_smul_of_pos (norm_pos_iff.mpr hy)]
    apply normalize_eq_self_of_norm_eq_one
    simpa only [mem_sphere, dist_zero_right] using u.val.property

theorem finite_unitSphereCone_fiber_iff
    (φ : sphere (0 : V) 1 → sphere (0 : V) 1) (y : V) (hy : y ≠ 0) (hyball : ‖y‖ ≤ 1) :
    {x : V | x ∈ closedBall (0 : V) 1 ∧ unitSphereCone φ x = y}.Finite ↔
      {u : sphere (0 : V) 1 | φ u = coneDirection y hy}.Finite :=
  (unitSphereConeFiberEquiv φ y hy hyball).set_finite_iff

theorem card_unitSphereCone_fiber
    (φ : sphere (0 : V) 1 → sphere (0 : V) 1) (y : V) (hy : y ≠ 0) (hyball : ‖y‖ ≤ 1) :
    Nat.card {x : V // x ∈ closedBall (0 : V) 1 ∧ unitSphereCone φ x = y} =
      Nat.card {u : sphere (0 : V) 1 // φ u = coneDirection y hy} :=
  Nat.card_congr (unitSphereConeFiberEquiv φ y hy hyball)

end BanachIsometric
