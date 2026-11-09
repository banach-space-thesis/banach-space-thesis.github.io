import BanachIsometric.NonvanishingConeSignedIndexHomotopy
import BanachIsometric.SignedIndexConnectedDensity
import BanachIsometric.CoordinateCube
import BanachIsometric.SignedCountCoordinateTransport
import BanachIsometric.SignedCountExcision

/-!
# The classical signed-fiber degree of a Lipschitz sphere map

The cone of a map between unit spheres preserves the norm. Its actual integer
count on the unit ball is almost everywhere the canonical local cone index.
This characterization will remove the auxiliary choice of coordinates.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def unitSphereCone (φ : sphere (0 : V) 1 → sphere (0 : V) 1) : V → V :=
  coneExtension (fun u => (φ u : V))

theorem norm_unitSphereCone (φ : sphere (0 : V) 1 → sphere (0 : V) 1) (x : V) :
    ‖unitSphereCone φ x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, unitSphereCone]
  rw [unitSphereCone, coneExtension_of_ne _ x hx, norm_smul,
    Real.norm_of_nonneg (norm_nonneg x)]
  have hu : ‖(φ (coneDirection x hx) : V)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (φ (coneDirection x hx)).property
  rw [hu, mul_one]

theorem unitSphereCone_eq_zero_iff (φ : sphere (0 : V) 1 → sphere (0 : V) 1) (x : V) :
    unitSphereCone φ x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, norm_unitSphereCone, norm_eq_zero]

variable [FiniteDimensional ℝ V]

theorem exists_lipschitz_unitSphereCone {φ : sphere (0 : V) 1 → sphere (0 : V) 1}
    {C : ℝ≥0} (hφ : LipschitzWith C φ) :
    ∃ L : ℝ≥0, LipschitzWith L (unitSphereCone φ) := by
  exact exists_lipschitz_coneExtension ((LipschitzWith.subtype_val _).comp hφ)

noncomputable def sphereConeCubeIndex {n : ℕ} [NeZero n]
    (e : V ≃L[ℝ] PiolaSpace n) (φ : sphere (0 : V) 1 → sphere (0 : V) 1) (R : ℝ) : ℤ :=
  localSignedIndex (coordinateMapConjugate e (unitSphereCone φ))
    (coordinateCubeLower n R) (coordinateCubeUpper n R) 0

theorem ae_coordinate_unitSphereCone_count_eq_cubeIndex
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {R : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R) :
    ∀ᵐ w, ‖e.symm w‖ < 1 →
      signedFiberCount (coordinateMapConjugate e (unitSphereCone φ))
        (fderiv ℝ (coordinateMapConjugate e (unitSphereCone φ)))
        (e '' closedBall (0 : V) 1) w = sphereConeCubeIndex e φ R := by
  let a := coordinateCubeLower n R
  let b := coordinateCubeUpper n R
  let F := coordinateMapConjugate e (unitSphereCone φ)
  let U : Set (PiolaSpace n) := {w | ‖e.symm w‖ < 1}
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hab : a ≤ b := coordinateCube_lower_le_upper n hRpos.le
  obtain ⟨L, hL⟩ := exists_lipschitz_unitSphereCone hφ
  have hF : LipschitzWith _ F := e.lipschitz.comp (hL.comp e.symm.lipschitz)
  have hUopen : IsOpen U := isOpen_lt e.symm.continuous.norm continuous_const
  have hUeq : e '' ball (0 : V) 1 = U := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [U, mem_setOf_eq, e.symm_apply_apply, mem_ball, dist_zero_right] using hx
    · intro hw
      exact ⟨e.symm w, by simpa only [mem_ball, dist_zero_right] using hw, e.apply_symm_apply w⟩
  have hU : IsPreconnected U := by
    rw [← hUeq]
    exact ((convex_ball (0 : V) 1).isConnected (nonempty_ball.mpr zero_lt_one)).isPreconnected.image
      e e.continuous.continuousOn
  have hnorm (x : PiolaSpace n) : ‖e.symm (F x)‖ = ‖e.symm x‖ := by
    simpa only [F, coordinateMapConjugate, e.symm_apply_apply] using norm_unitSphereCone φ (e.symm x)
  have havoid : Disjoint U (F '' piolaBoxBoundary a b) := by
    apply Set.disjoint_left.mpr
    rintro _ hw ⟨x, hx, rfl⟩
    have hgt := coordinateCube_boundary_preimage_norm_gt_one e hR hx
    change ‖e.symm (F x)‖ < 1 at hw
    rw [hnorm] at hw
    linarith
  have hc : (0 : PiolaSpace n) ∈ U := by simp [U]
  have hcount := ae_signedFiberCount_eq_localSignedIndex_on_preconnected hF a b hab hUopen hU havoid hc
  filter_upwards [hcount] with w hw
  intro hwm
  have hexc := signedFiberCount_congr_source_on_fiber F (fderiv ℝ F)
    (s := Icc a b) (t := e '' closedBall (0 : V) 1) w ?_
  · exact hexc.symm.trans (hw hwm)
  · intro x hfx
    have hxnorm : ‖e.symm x‖ < 1 := by rw [← hnorm, hfx]; exact hwm
    have hxball : e.symm x ∈ closedBall (0 : V) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hxnorm.le
    have hxcube := coordinate_image_unitBall_mem_cube e hR.le hxball
    rw [e.apply_symm_apply] at hxcube
    exact ⟨fun _ => ⟨e.symm x, hxball, e.apply_symm_apply x⟩, fun _ => hxcube⟩

variable [MeasurableSpace V] [BorelSpace V]

theorem ae_unitSphereCone_count_eq_cubeIndex
    (μ : Measure V) [μ.IsAddHaarMeasure] {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {R : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R) :
    ∀ᵐ v ∂μ, v ∈ ball (0 : V) 1 →
      signedFiberCount (unitSphereCone φ) (fderiv ℝ (unitSphereCone φ))
        (closedBall (0 : V) 1) v = sphereConeCubeIndex e φ R := by
  apply (ae_signedFiberCount_eq_on_image_iff_of_isAddHaarMeasure μ volume e
    (unitSphereCone φ) (closedBall (0 : V) 1) (ball (0 : V) 1) _).mp
  filter_upwards [ae_coordinate_unitSphereCone_count_eq_cubeIndex e hφ hR] with w hw
  rintro ⟨x, hx, rfl⟩
  apply hw
  simpa only [e.symm_apply_apply, mem_ball, dist_zero_right] using hx

end BanachIsometric
