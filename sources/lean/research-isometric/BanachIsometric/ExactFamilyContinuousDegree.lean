import BanachIsometric.ExactFamilyRigidity
import BanachIsometric.ContinuousSphereSignedDegree

/-!
# Exact-family rigidity with the paper's merely continuous normal map

The normal map in Theorem 3.1 is continuous, not required to be Lipschitz.
Its degree is the proved continuous extension of the actual signed count.
The normalized evaluation is Lipschitz, and its actual orthogonal homotopy
to the normal map identifies those degrees without extra regularity.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)
  {n : ℕ} [NeZero n]

noncomputable def continuousNormalDegree (e : V ≃L[ℝ] PiolaSpace n) : ℤ :=
  continuousSphereSignedDegree e A.normal

theorem coneEvaluation_cubeIndex_eq_continuousNormalDegree
    (e : V ≃L[ℝ] PiolaSpace n) (hg0 : g 0 = 0) {y : E} (hy : 0 < p y) :
    localSignedIndex (coordinateMapConjugate e (A.coneEvaluation y))
      (coordinateCubeLower n (‖(e : V →L[ℝ] PiolaSpace n)‖ + 1))
      (coordinateCubeUpper n (‖(e : V →L[ℝ] PiolaSpace n)‖ + 1)) 0 =
      A.continuousNormalDegree e := by
  let R := ‖(e : V →L[ℝ] PiolaSpace n)‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  rw [A.coneEvaluation_localSignedIndex_eq_direction e hg0 hy _ _
    (coordinateCube_lower_le_upper n hR.le) (zero_mem_interior_coordinateCube n hR)]
  change sphereSignedDegree e (A.direction hg0 hy) = continuousSphereSignedDegree e A.normal
  obtain ⟨L, hL⟩ := A.exists_lipschitz_direction hg0 hy
  rw [← continuousSphereSignedDegree_eq_sphereSignedDegree e _ hL]
  exact (continuousSphereSignedDegree_eq_of_homotopy e (A.normalDirectionHomotopy hg0 hy)).symm

theorem ae_coordinate_unitBall_count_eq_continuousNormalDegree
    (e : V ≃L[ℝ] PiolaSpace n) (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    {y : E} (hy : 0 < p y) :
    ∀ᵐ v, g (e.symm v) < p y →
      signedFiberCount (coordinateMapConjugate e (A.coneEvaluation y))
        (fderiv ℝ (coordinateMapConjugate e (A.coneEvaluation y)))
        (e '' closedBall (0 : V) 1) v = A.continuousNormalDegree e := by
  let R := ‖(e : V →L[ℝ] PiolaSpace n)‖ + 1
  let a := coordinateCubeLower n R
  let b := coordinateCubeUpper n R
  let F := coordinateMapConjugate e (A.coneEvaluation y)
  let U : Set (PiolaSpace n) := {v | g (e.symm v) < p y}
  have hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R := by dsimp [R]; linarith
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hab : a ≤ b := coordinateCube_lower_le_upper n hRpos.le
  obtain ⟨L, hL⟩ := A.exists_lipschitz_coneEvaluation y
  have hF : LipschitzWith _ F := e.lipschitz.comp (hL.comp e.symm.lipschitz)
  have hUopen : IsOpen U := isOpen_lt (hcont.comp e.symm.continuous) continuous_const
  have hUeq : e '' {v : V | g v < p y} = U := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [U, mem_setOf_eq, e.symm_apply_apply] using hx
    · intro hv
      exact ⟨e.symm v, hv, e.apply_symm_apply v⟩
  have hU : IsPreconnected U := by
    rw [← hUeq]
    exact (hg.isPreconnected_strict_sublevel hy).image e e.continuous.continuousOn
  have havoid : Disjoint U (F '' piolaBoxBoundary a b) := by
    apply Set.disjoint_left.mpr
    intro v hv himage
    obtain ⟨x, hx, rfl⟩ := himage
    have hnorm := coordinateCube_boundary_preimage_norm_gt_one e hR hx
    have hga : g (e.symm (F x)) = ‖e.symm x‖ * p y := by
      simpa only [F, coordinateMapConjugate, e.symm_apply_apply] using
        A.gauge_coneEvaluation hg y (e.symm x)
    change g (e.symm (F x)) < p y at hv
    rw [hga] at hv
    nlinarith
  have hc : (0 : PiolaSpace n) ∈ U := by
    simpa only [U, mem_setOf_eq, map_zero, (hg.eq_zero_iff 0).mpr rfl] using hy
  have hcount := ae_signedFiberCount_eq_localSignedIndex_on_preconnected hF a b hab hUopen hU havoid hc
  have hindex := A.coneEvaluation_cubeIndex_eq_continuousNormalDegree e ((hg.eq_zero_iff 0).mpr rfl) hy
  filter_upwards [hcount] with v hv
  intro hvg
  have hexc := signedFiberCount_congr_source_on_fiber F (fderiv ℝ F)
    (s := Icc a b) (t := e '' closedBall (0 : V) 1) v ?_
  · exact hexc.symm.trans ((hv hvg).trans hindex)
  · intro x hfx
    have hga : g (e.symm v) = ‖e.symm x‖ * p y := by
      rw [← hfx]
      simpa only [F, coordinateMapConjugate, e.symm_apply_apply] using
        A.gauge_coneEvaluation hg y (e.symm x)
    have hnorm : ‖e.symm x‖ < 1 := by rw [hga] at hvg; nlinarith
    have hxball : e.symm x ∈ closedBall (0 : V) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hnorm.le
    have hxcube := coordinate_image_unitBall_mem_cube e hR.le hxball
    rw [e.apply_symm_apply] at hxcube
    exact ⟨fun _ => ⟨e.symm x, hxball, e.apply_symm_apply x⟩, fun _ => hxcube⟩

variable [MeasurableSpace V] [BorelSpace V]

theorem ae_interior_body_count_eq_continuousNormalDegree
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (e : V ≃L[ℝ] PiolaSpace n) (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    {y : E} (hy : 0 < p y) :
    ∀ᵐ v ∂μ, v ∈ interior {v | g v ≤ p y} →
      signedFiberCount (A.coneEvaluation y) (fderiv ℝ (A.coneEvaluation y))
        (closedBall (0 : V) 1) v = A.continuousNormalDegree e := by
  have hraw : ∀ᵐ v ∂μ, g v < p y →
      signedFiberCount (A.coneEvaluation y) (fderiv ℝ (A.coneEvaluation y))
        (closedBall (0 : V) 1) v = A.continuousNormalDegree e := by
    apply (ae_signedFiberCount_eq_on_image_iff_of_isAddHaarMeasure μ volume e
      (A.coneEvaluation y) (closedBall (0 : V) 1) {v | g v < p y} _).mp
    filter_upwards [A.ae_coordinate_unitBall_count_eq_continuousNormalDegree e hg hcont hy] with v hv
    rintro ⟨x, hx, rfl⟩
    exact hv (by simpa only [e.symm_apply_apply] using hx)
  simpa only [hg.interior_pos_sublevel_eq_strict hcont hy, mem_setOf_eq] using hraw

end BanachIsometric.ExactTangentialFamily
