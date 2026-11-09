import BanachIsometric.SphereSignedDegree
import BanachIsometric.LocalSignedIndexContinuity

/-! The actual cone index at every interior unit-ball target equals the
constructed sphere degree, by proved connected local-index constancy. -/

namespace BanachIsometric

open Set Metric
open scoped NNReal

theorem sphereCone_interior_index_eq_sphereSignedDegree
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    {φ : sphere (0 : V) 1 → sphere (0 : V) 1} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {v : V} (hv : ‖v‖ < 1) :
    localSignedIndex (coordinateMapConjugate e (unitSphereCone φ))
      (coordinateCubeLower n (‖(e : V →L[ℝ] PiolaSpace n)‖ + 1))
      (coordinateCubeUpper n (‖(e : V →L[ℝ] PiolaSpace n)‖ + 1)) (e v) =
      sphereSignedDegree e φ := by
  let R := ‖(e : V →L[ℝ] PiolaSpace n)‖ + 1
  let a := coordinateCubeLower n R
  let b := coordinateCubeUpper n R
  let F := coordinateMapConjugate e (unitSphereCone φ)
  let U : Set (PiolaSpace n) := e '' ball (0 : V) 1
  have hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R := by dsimp [R]; linarith
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hab : a ≤ b := coordinateCube_lower_le_upper n hRpos.le
  obtain ⟨L, hL⟩ := exists_lipschitz_unitSphereCone hφ
  have hF : LipschitzWith _ F := e.lipschitz.comp (hL.comp e.symm.lipschitz)
  have hU : IsPreconnected U :=
    ((convex_ball (0 : V) 1).isConnected (nonempty_ball.mpr zero_lt_one)).isPreconnected.image
      e e.continuous.continuousOn
  have hsub : U ⊆ (F '' piolaBoxBoundary a b)ᶜ := by
    rintro _ ⟨w, hw, rfl⟩ ⟨z, hz, hzw⟩
    have hgt := coordinateCube_boundary_preimage_norm_gt_one e hR hz
    have hzw' : unitSphereCone φ (e.symm z) = w := by
      apply e.injective
      exact hzw
    have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    rw [← hzw', norm_unitSphereCone] at hw'
    linarith
  have hvU : e v ∈ U := ⟨v, by simpa only [mem_ball, dist_zero_right] using hv, rfl⟩
  have hzeroU : (0 : PiolaSpace n) ∈ U :=
    ⟨0, mem_ball_self zero_lt_one, e.map_zero⟩
  exact localSignedIndex_eq_on_preconnected hF a b hab hU hsub hvU hzeroU

end BanachIsometric
