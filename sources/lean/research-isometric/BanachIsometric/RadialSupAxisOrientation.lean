import BanachIsometric.SupGaugeAxisSmooth
import BanachIsometric.RadialJacobianOrientation

/-! # Positive actual Jacobian of the cube-to-disk radial map at the first axis -/

namespace BanachIsometric

open scoped Topology

theorem radialGaugeMapInv_sup_axis (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    radialGaugeMapInv (coordinateSupGauge (n + 1)) (EuclideanSpace.single 0 r) =
      EuclideanSpace.single 0 r := by
  have hg : coordinateSupGauge (n + 1) (EuclideanSpace.single 0 r) = |r| := by
    have h := (coordinateSupGauge_eventually_eq_abs_first n r hr).self_of_nhds
    simpa [EuclideanSpace.single_apply] using h
  rw [radialGaugeMapInv, hg, EuclideanSpace.norm_single, Real.norm_eq_abs,
    div_self (abs_ne_zero.mpr hr), one_smul]

theorem det_fderiv_radialGaugeMapInv_sup_axis_pos (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    0 < (fderiv ℝ (radialGaugeMapInv (coordinateSupGauge (n + 1)))
      (EuclideanSpace.single 0 r)).det := by
  let x : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 r
  have hx : x ≠ 0 := by
    intro hz
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v 0) hz
    exact hr (by simpa [x, EuclideanSpace.single_apply] using h)
  let a : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun z => coordinateSupGauge (n + 1) z / ‖z‖
  have hcont : ContDiffAt ℝ 1 a x :=
    (contDiffAt_coordinateSupGauge_axis n r hr 1).div (contDiffAt_norm ℝ hx) (norm_ne_zero_iff.mpr hx)
  have ha : HasFDerivAt a (fderiv ℝ a x) x := (hcont.differentiableAt (by norm_num)).hasFDerivAt
  have hscale : ∀ t : ℝ, 0 < t → a (t • x) = a x := by
    intro t ht
    dsimp [a]
    rw [(coordinateSupGauge_homogeneous (n + 1)).smul_nonneg t ht.le,
      norm_smul, Real.norm_of_nonneg ht.le]
    exact mul_div_mul_left _ _ ht.ne'
  have hpos : 0 < a x := div_pos ((coordinateSupGauge_homogeneous (n + 1)).pos hx)
    (norm_pos_iff.mpr hx)
  simpa only [a, radialGaugeMapInv] using det_fderiv_radial_pos ha hscale hpos

end BanachIsometric
