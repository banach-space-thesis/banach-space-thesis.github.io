import BanachIsometric.ExactFamilySignedIndex
import BanachIsometric.SignedIndexConnectedDensity
import BanachIsometric.CoordinateCube
import BanachIsometric.HomogeneousSublevelConnected
import BanachIsometric.SignedCountCoordinateTransport
import BanachIsometric.SignedCountExcision

/-!
# Actual evaluated-cone density on the strict target body

A sufficiently large actual coordinate cube has boundary preimages of norm
greater than one. The exact gauge identity puts its boundary image beyond the
target body. Connected density identifies the integer count there with the
normal cone index. The same gauge identity forces all fibers over the strict
target body into the actual Euclidean unit ball, allowing exact excision and
transport to the original Haar measure.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)
  {n : ℕ} [NeZero n]

theorem ae_coordinate_coneEvaluation_count_eq_normal_index
    (e : V ≃L[ℝ] PiolaSpace n) (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    {y : E} (hy : 0 < p y) (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    {R : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R) :
    ∀ᵐ v, g (e.symm v) < p y →
      signedFiberCount (coordinateMapConjugate e (A.coneEvaluation y))
        (fderiv ℝ (coordinateMapConjugate e (A.coneEvaluation y)))
        (Icc (coordinateCubeLower n R) (coordinateCubeUpper n R)) v =
      localSignedIndex (coordinateMapConjugate e (coneExtension (fun z => (A.normal z).val)))
        (coordinateCubeLower n R) (coordinateCubeUpper n R) 0 := by
  let a := coordinateCubeLower n R
  let b := coordinateCubeUpper n R
  let F := coordinateMapConjugate e (A.coneEvaluation y)
  let U : Set (PiolaSpace n) := {v | g (e.symm v) < p y}
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hab : a ≤ b := coordinateCube_lower_le_upper n hRpos.le
  have hzero : (0 : PiolaSpace n) ∈ interior (Icc a b) := zero_mem_interior_coordinateCube n hRpos
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
  have hindex := A.coneEvaluation_localSignedIndex_eq_normal e ((hg.eq_zero_iff 0).mpr rfl)
    hy hnormal a b hab hzero
  simpa only [F, a, b, U, mem_setOf_eq, hindex] using hcount

theorem ae_coordinate_unitBall_count_eq_normal_index
    (e : V ≃L[ℝ] PiolaSpace n) (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    {y : E} (hy : 0 < p y) (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    {R : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R) :
    ∀ᵐ v, g (e.symm v) < p y →
      signedFiberCount (coordinateMapConjugate e (A.coneEvaluation y))
        (fderiv ℝ (coordinateMapConjugate e (A.coneEvaluation y)))
        (e '' closedBall (0 : V) 1) v =
      localSignedIndex (coordinateMapConjugate e (coneExtension (fun z => (A.normal z).val)))
        (coordinateCubeLower n R) (coordinateCubeUpper n R) 0 := by
  filter_upwards [A.ae_coordinate_coneEvaluation_count_eq_normal_index e hg hcont hy hnormal hR] with v hv
  intro hvg
  have hexc := signedFiberCount_congr_source_on_fiber
    (coordinateMapConjugate e (A.coneEvaluation y))
    (fderiv ℝ (coordinateMapConjugate e (A.coneEvaluation y)))
    (s := Icc (coordinateCubeLower n R) (coordinateCubeUpper n R))
    (t := e '' closedBall (0 : V) 1) v ?_
  · exact hexc.symm.trans (hv hvg)
  · intro x hfx
    have hga : g (e.symm v) = ‖e.symm x‖ * p y := by
      rw [← hfx]
      simpa only [coordinateMapConjugate, e.symm_apply_apply] using
        A.gauge_coneEvaluation hg y (e.symm x)
    have hnorm : ‖e.symm x‖ < 1 := by rw [hga] at hvg; nlinarith
    have hxball : e.symm x ∈ closedBall (0 : V) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hnorm.le
    have hxcube := coordinate_image_unitBall_mem_cube e hR.le hxball
    rw [e.apply_symm_apply] at hxcube
    exact ⟨fun _ => ⟨e.symm x, hxball, e.apply_symm_apply x⟩, fun _ => hxcube⟩

variable [MeasurableSpace V] [BorelSpace V]

theorem ae_unitBall_coneEvaluation_count_eq_normal_index
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (e : V ≃L[ℝ] PiolaSpace n) (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    {y : E} (hy : 0 < p y) (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    {R : ℝ} (hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < R) :
    ∀ᵐ v ∂μ, g v < p y → signedFiberCount (A.coneEvaluation y) (fderiv ℝ (A.coneEvaluation y))
      (closedBall (0 : V) 1) v =
      localSignedIndex (coordinateMapConjugate e (coneExtension (fun z => (A.normal z).val)))
        (coordinateCubeLower n R) (coordinateCubeUpper n R) 0 := by
  apply (ae_signedFiberCount_eq_on_image_iff_of_isAddHaarMeasure μ volume e
    (A.coneEvaluation y) (closedBall (0 : V) 1) {v | g v < p y} _).mp
  filter_upwards [A.ae_coordinate_unitBall_count_eq_normal_index e hg hcont hy hnormal hR] with v hv
  rintro ⟨x, hx, rfl⟩
  exact hv (by simpa only [e.symm_apply_apply] using hx)

end BanachIsometric.ExactTangentialFamily
