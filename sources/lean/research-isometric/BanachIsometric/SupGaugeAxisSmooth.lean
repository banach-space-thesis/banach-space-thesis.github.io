import BanachIsometric.CubeDiskCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The actual coordinate sup gauge agrees locally with the absolute first
coordinate at every nonzero first-axis point. Consequently the actual radial
map and inverse are smooth there in the original Euclidean coordinates. -/

noncomputable section
namespace BanachIsometric
open Set
open scoped Topology

theorem coordinateSupGauge_eventually_eq_abs_first (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    coordinateSupGauge (n + 1) =ᶠ[𝓝 (EuclideanSpace.single 0 r)]
      (fun z : EuclideanSpace ℝ (Fin (n + 1)) => |z 0|) := by
  have hcoord (i : Fin (n + 1)) :
      Continuous (fun z : EuclideanSpace ℝ (Fin (n + 1)) => |z i|) :=
    ((continuous_apply i).comp (euclideanCoordinates (n + 1)).continuous).abs
  have hall : ∀ᶠ z : EuclideanSpace ℝ (Fin (n + 1)) in 𝓝 (EuclideanSpace.single 0 r),
      ∀ j : Fin (n + 1), j ≠ 0 → |z j| < |z 0| := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hj).elim)
    · have hlt : |(EuclideanSpace.single 0 r : EuclideanSpace ℝ (Fin (n + 1))) j| <
          |(EuclideanSpace.single 0 r : EuclideanSpace ℝ (Fin (n + 1))) 0| := by
        simpa [EuclideanSpace.single_apply, Pi.single_apply, hj] using abs_pos.mpr hr
      filter_upwards [(isOpen_lt (hcoord j) (hcoord 0)).mem_nhds hlt] with z hz
      intro _
      exact hz
  filter_upwards [hall] with z hz
  change ‖euclideanCoordinates (n + 1) z‖ = |z 0|
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro j
    change |z j| ≤ |z 0|
    by_cases hj : j = 0
    · subst j
      exact le_rfl
    · exact (hz j hj).le
  · exact norm_le_pi_norm (euclideanCoordinates (n + 1) z) 0

theorem contDiffAt_coordinateSupGauge_axis (n : ℕ) (r : ℝ) (hr : r ≠ 0)
    (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (coordinateSupGauge (n + 1)) (EuclideanSpace.single 0 r) := by
  let a : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj 0).comp (euclideanCoordinates (n + 1)).toContinuousLinearMap
  have ha : a (EuclideanSpace.single 0 r) ≠ 0 := by
    simpa [a, EuclideanSpace.single_apply, Pi.single_apply] using hr
  have habs : ContDiffAt ℝ k (fun z => |a z|) (EuclideanSpace.single 0 r) := by
    simpa only [Real.norm_eq_abs] using (a.contDiff.contDiffAt.norm ℝ ha)
  exact habs.congr_of_eventuallyEq (coordinateSupGauge_eventually_eq_abs_first n r hr)

theorem contDiffAt_radialGaugeMapInv_sup_axis (n : ℕ) (r : ℝ) (hr : r ≠ 0)
    (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (radialGaugeMapInv (coordinateSupGauge (n + 1))) (EuclideanSpace.single 0 r) := by
  have hx : (EuclideanSpace.single 0 r : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
    intro he
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z 0) he
    exact hr (by simpa [EuclideanSpace.single_apply, Pi.single_apply] using h)
  exact ((contDiffAt_coordinateSupGauge_axis n r hr k).div
    (contDiffAt_norm ℝ hx) (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem contDiffAt_radialGaugeMap_sup_axis (n : ℕ) (r : ℝ) (hr : r ≠ 0)
    (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (radialGaugeMap (coordinateSupGauge (n + 1))) (EuclideanSpace.single 0 r) := by
  have hx : (EuclideanSpace.single 0 r : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
    intro he
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z 0) he
    exact hr (by simpa [EuclideanSpace.single_apply, Pi.single_apply] using h)
  exact ((contDiffAt_norm ℝ hx).div (contDiffAt_coordinateSupGauge_axis n r hr k)
    ((coordinateSupGauge_homogeneous (n + 1)).pos hx).ne').smul contDiffAt_id

end BanachIsometric
