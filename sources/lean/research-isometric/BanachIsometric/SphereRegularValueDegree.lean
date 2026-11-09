import BanachIsometric.RegularValueSignedIndex
import BanachIsometric.SphereConeInteriorIndex
import BanachIsometric.SignedCountCoordinateTransport

/-!
# Computing the actual sphere degree at one ordinary regular cone value

The canonical cone index is constant throughout the interior unit ball.
The proved regular-value index formula evaluates it at a single actual
target there. Cone norm preservation gives exact source excision and genuine
coordinate transport. Finite fibers are a conclusion, not a premise.
-/

namespace BanachIsometric

open Set Metric
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem sphereSignedDegree_eq_signedFiberCount_of_regular_value
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {v : V} (hv : ‖v‖ < 1)
    (hreg : ∀ x ∈ closedBall (0 : V) 1, unitSphereCone φ x = v →
      DifferentiableAt ℝ (unitSphereCone φ) x ∧ (fderiv ℝ (unitSphereCone φ) x).det ≠ 0) :
    sphereSignedDegree e φ = signedFiberCount (unitSphereCone φ)
      (fderiv ℝ (unitSphereCone φ)) (closedBall (0 : V) 1) v := by
  let R := ‖(e : V →L[ℝ] PiolaSpace n)‖ + 1
  let a := coordinateCubeLower n R
  let b := coordinateCubeUpper n R
  let F := coordinateMapConjugate e (unitSphereCone φ)
  have hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R := by dsimp [R]; linarith
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hab : a ≤ b := coordinateCube_lower_le_upper n hRpos.le
  obtain ⟨L, hL⟩ := exists_lipschitz_unitSphereCone hφ
  have hF : LipschitzWith _ F := e.lipschitz.comp (hL.comp e.symm.lipschitz)
  have hpre (z : PiolaSpace n) (hz : F z = e v) : unitSphereCone φ (e.symm z) = v :=
    e.injective hz
  have hball (z : PiolaSpace n) (hz : F z = e v) : e.symm z ∈ closedBall (0 : V) 1 := by
    have hn : ‖e.symm z‖ = ‖v‖ := by rw [← norm_unitSphereCone φ, hpre z hz]
    simpa only [mem_closedBall, dist_zero_right, hn] using hv.le
  have hc : e v ∉ F '' piolaBoxBoundary a b := by
    rintro ⟨z, hz, hzc⟩
    have hgt := coordinateCube_boundary_preimage_norm_gt_one e hR hz
    have hn : ‖e.symm z‖ = ‖v‖ := by rw [← norm_unitSphereCone φ, hpre z hzc]
    linarith
  have hregF : ∀ z ∈ Icc a b, F z = e v →
      DifferentiableAt ℝ F z ∧ (fderiv ℝ F z).det ≠ 0 := by
    intro z _hz hzc
    obtain ⟨hdiff, hdet⟩ := hreg (e.symm z) (hball z hzc) (hpre z hzc)
    constructor
    · exact e.hasFDerivAt.differentiableAt.comp z (hdiff.comp z e.symm.hasFDerivAt.differentiableAt)
    · have heq := det_fderiv_coordinateConjugate e (unitSphereCone φ) (e.symm z)
      rw [e.apply_symm_apply] at heq
      rw [heq]
      exact hdet
  have hindex := localSignedIndex_eq_signedFiberCount_of_regular_value hF a b hab (e v) hc hregF
  have hexc := signedFiberCount_congr_source_on_fiber F (fderiv ℝ F)
    (s := Icc a b) (t := e '' closedBall (0 : V) 1) (e v) (fun z hzc => by
      have hzball := hball z hzc
      have hzcube := coordinate_image_unitBall_mem_cube e hR.le hzball
      rw [e.apply_symm_apply] at hzcube
      exact ⟨fun _ => ⟨e.symm z, hzball, e.apply_symm_apply z⟩, fun _ => hzcube⟩)
  calc
    sphereSignedDegree e φ = localSignedIndex F a b (e v) :=
      (sphereCone_interior_index_eq_sphereSignedDegree e hφ hv).symm
    _ = signedFiberCount F (fderiv ℝ F) (Icc a b) (e v) := hindex
    _ = signedFiberCount F (fderiv ℝ F) (e '' closedBall (0 : V) 1) (e v) := hexc
    _ = signedFiberCount (unitSphereCone φ) (fderiv ℝ (unitSphereCone φ)) (closedBall (0 : V) 1) v :=
      signedFiberCount_coordinateConjugate e (unitSphereCone φ) (closedBall (0 : V) 1) v

theorem sphereSignedDegree_eq_natCard_of_positive_regular_value
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {v : V} (hv : ‖v‖ < 1)
    (hdiff : ∀ x ∈ closedBall (0 : V) 1, unitSphereCone φ x = v →
      DifferentiableAt ℝ (unitSphereCone φ) x)
    (hpos : ∀ x ∈ closedBall (0 : V) 1, unitSphereCone φ x = v →
      0 < (fderiv ℝ (unitSphereCone φ) x).det) :
    sphereSignedDegree e φ =
      (Nat.card {x : V // x ∈ closedBall (0 : V) 1 ∧ unitSphereCone φ x = v} : ℤ) := by
  have hreg (x) (hx : x ∈ closedBall (0 : V) 1) (hxc : unitSphereCone φ x = v) :=
    And.intro (hdiff x hx hxc) (hpos x hx hxc).ne'
  obtain ⟨L, hL⟩ := exists_lipschitz_unitSphereCone hφ
  have hfin : {x : V | x ∈ closedBall (0 : V) 1 ∧ unitSphereCone φ x = v}.Finite := by
    have h := finite_actual_regular_fiber (isCompact_closedBall _ _) hL.continuous.continuousOn hreg
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_singleton_iff] using h
  rw [sphereSignedDegree_eq_signedFiberCount_of_regular_value e hφ hv hreg]
  exact signedFiberCount_eq_card_of_pos_det (unitSphereCone φ) (fderiv ℝ (unitSphereCone φ))
    (closedBall (0 : V) 1) v hfin hpos

end BanachIsometric
