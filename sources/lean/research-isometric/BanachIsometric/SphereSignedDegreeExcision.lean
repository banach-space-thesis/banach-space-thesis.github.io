import BanachIsometric.SphereSignedDegree
import BanachIsometric.SignedIndexExcision

/-!
# Independence from every positive coordinate-cube radius

Norm preservation of the actual sphere cone forces every sufficiently
small-target fiber into both source cubes. Actual integer excision therefore
identifies the local indices even when neither cube encloses the unit ball.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_le_mul_norm_coordinate_unitSphereCone
    {n : ℕ} (e : V ≃L[ℝ] PiolaSpace n)
    (φ : sphere (0 : V) 1 → sphere (0 : V) 1) (x : PiolaSpace n) :
    ‖x‖ ≤ (‖(e : V →L[ℝ] PiolaSpace n)‖ * ‖(e.symm : PiolaSpace n →L[ℝ] V)‖) *
      ‖coordinateMapConjugate e (unitSphereCone φ) x‖ := by
  have hx := (e : V →L[ℝ] PiolaSpace n).le_opNorm (e.symm x)
  change ‖e (e.symm x)‖ ≤ ‖(e : V →L[ℝ] PiolaSpace n)‖ * ‖e.symm x‖ at hx
  rw [e.apply_symm_apply] at hx
  have hnorm : ‖e.symm (coordinateMapConjugate e (unitSphereCone φ) x)‖ = ‖e.symm x‖ := by
    simpa only [coordinateMapConjugate, e.symm_apply_apply] using norm_unitSphereCone φ (e.symm x)
  have hy := (e.symm : PiolaSpace n →L[ℝ] V).le_opNorm
    (coordinateMapConjugate e (unitSphereCone φ) x)
  change ‖e.symm (coordinateMapConjugate e (unitSphereCone φ) x)‖ ≤
    ‖(e.symm : PiolaSpace n →L[ℝ] V)‖ * ‖coordinateMapConjugate e (unitSphereCone φ) x‖ at hy
  rw [hnorm] at hy
  calc
    ‖x‖ ≤ ‖(e : V →L[ℝ] PiolaSpace n)‖ * ‖e.symm x‖ := hx
    _ ≤ ‖(e : V →L[ℝ] PiolaSpace n)‖ *
        (‖(e.symm : PiolaSpace n →L[ℝ] V)‖ * ‖coordinateMapConjugate e (unitSphereCone φ) x‖) :=
      mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = _ := by ring

theorem coordinate_unitSphereCone_eq_zero_iff
    {n : ℕ} (e : V ≃L[ℝ] PiolaSpace n)
    (φ : sphere (0 : V) 1 → sphere (0 : V) 1) (x : PiolaSpace n) :
    coordinateMapConjugate e (unitSphereCone φ) x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hbound := norm_le_mul_norm_coordinate_unitSphereCone e φ x
    rw [hx, norm_zero, mul_zero] at hbound
    exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
  · intro hx
    simp only [hx, coordinateMapConjugate, map_zero, unitSphereCone, coneExtension_zero]

variable [FiniteDimensional ℝ V]

theorem sphereConeCubeIndex_eq_of_pos_radii
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    sphereConeCubeIndex e φ R = sphereConeCubeIndex e φ S := by
  let F := coordinateMapConjugate e (unitSphereCone φ)
  obtain ⟨L, hL⟩ := exists_lipschitz_unitSphereCone hφ
  have hF : LipschitzWith _ F := e.lipschitz.comp (hL.comp e.symm.lipschitz)
  have hboundary (T : ℝ) (hT : 0 < T) :
      (0 : PiolaSpace n) ∉ F '' piolaBoxBoundary (coordinateCubeLower n T) (coordinateCubeUpper n T) := by
    rintro ⟨x, hx, hFx⟩
    have hx0 := (coordinate_unitSphereCone_eq_zero_iff e φ x).mp hFx
    subst x
    rw [piolaBoxBoundary_eq_frontier, frontier] at hx
    exact hx.2 (zero_mem_interior_coordinateCube n hT)
  let B : ℝ := ‖(e : V →L[ℝ] PiolaSpace n)‖ * ‖(e.symm : PiolaSpace n →L[ℝ] V)‖
  let δ : ℝ := min R S / (B + 1)
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hBpos : 0 < B + 1 := by linarith
  have hδ : 0 < δ := div_pos (lt_min hR hS) hBpos
  have hδeq : δ * (B + 1) = min R S := div_mul_cancel₀ _ hBpos.ne'
  apply localSignedIndex_eq_of_source_congr hF
    (coordinateCubeLower n R) (coordinateCubeUpper n R)
    (coordinateCubeLower n S) (coordinateCubeUpper n S)
    (coordinateCube_lower_le_upper n hR.le) (coordinateCube_lower_le_upper n hS.le) 0
    (hboundary R hR) (hboundary S hS) hδ
  intro y hy x hxy
  have hyδ : ‖y‖ < δ := by simpa only [mem_ball, dist_zero_right] using hy
  have hbound : ‖x‖ ≤ B * ‖y‖ := by
    simpa only [F, hxy] using norm_le_mul_norm_coordinate_unitSphereCone e φ x
  have hxsmall : ‖x‖ < min R S := by
    calc
      ‖x‖ ≤ B * ‖y‖ := hbound
      _ ≤ (B + 1) * ‖y‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (B + 1) * δ := mul_lt_mul_of_pos_left hyδ hBpos
      _ = min R S := by nlinarith [hδeq]
  have hxR := mem_coordinateCube_of_norm_le ((hxsmall.trans_le (min_le_left R S)).le)
  have hxS := mem_coordinateCube_of_norm_le ((hxsmall.trans_le (min_le_right R S)).le)
  exact ⟨fun _ => hxS, fun _ => hxR⟩

theorem sphereConeCubeIndex_eq_sphereSignedDegree_of_pos
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {R : ℝ} (hR : 0 < R) : sphereConeCubeIndex e φ R = sphereSignedDegree e φ := by
  apply sphereConeCubeIndex_eq_of_pos_radii e hφ hR
  positivity

end BanachIsometric
