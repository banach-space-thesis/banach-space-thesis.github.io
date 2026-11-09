/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Adapted from commit c66523531ff172d7f41913d94e56921e790a1b47 of
Vilin97/homotopy-groups-lean, examples/submissions/
sphere_lower_homotopy_subsingleton/Submission/SphereGenerator.lean.
Only the actual Euclidean disk quotient construction is ported here;
no external challenge declarations or CW/classification assumptions are used.
-/
import BanachIsometric.CoordinateOrthogonality
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Topology unitInterval
noncomputable section
namespace BanachIsometric.SphereGenerator

abbrev Sph (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

def sphereBasepoint (n : ℕ) : Sph n :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_single]
    norm_num⟩

theorem eq_of_sq_eq_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  nlinarith

theorem norm_eq_one_of_norm_sq_eq_one {E : Type*} [NormedAddCommGroup E] {y : E}
    (h : ‖y‖ ^ 2 = 1) : ‖y‖ = 1 := by nlinarith [norm_nonneg y]

/-- Prepend one coordinate to a Euclidean vector. -/
noncomputable def consLp {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons a (WithLp.ofLp v))

@[simp]
theorem consLp_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    consLp a v 0 = a := by
  simp [consLp]

@[simp]
theorem consLp_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    consLp a v i.succ = v i := by
  simp [consLp]

/-- The squared Euclidean norm after prepending a coordinate. -/
theorem norm_consLp_sq {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖consLp a v‖ ^ 2 = a ^ 2 + ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp [Real.norm_eq_abs]

/-- Prepending a coordinate is continuous in both inputs. -/
theorem continuous_consLp {n : ℕ} :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => consLp p.1 p.2) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp (continuous_pi fun i => ?_)
  induction i using Fin.cases with
  | zero => simpa [consLp] using continuous_fst
  | succ i =>
      simpa [consLp] using
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp' continuous_snd

/-- Every Euclidean vector splits into its first coordinate and its remaining coordinates. -/
theorem eq_consLp {n : ℕ} (z : EuclideanSpace ℝ (Fin (n + 1))) :
    z = consLp (z 0) (WithLp.toLp 2 fun i : Fin n => z i.succ) := by
  apply PiLp.ext
  intro i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- The first coordinate and the tail of a point on `Sⁿ` satisfy the unit-sphere equation. -/
theorem sphere_first_tail_norm_sq {n : ℕ} (z : Sph n) :
    (z.val 0) ^ 2 + ‖WithLp.toLp 2 (fun i : Fin n => z.val i.succ)‖ ^ 2 = 1 := by
  have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  rw [← norm_consLp_sq, ← eq_consLp z.val, hz]
  norm_num

/-- The ambient vector underlying the standard disk-to-sphere quotient map. -/
noncomputable def diskSphereFun (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  let v : EuclideanSpace ℝ (Fin n) := x.val
  consLp (2 * ‖v‖ ^ 2 - 1) ((2 * √(1 - ‖v‖ ^ 2) : ℝ) • v)

/-- The disk-to-sphere formula has unit norm. -/
theorem norm_diskSphereFun (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ‖diskSphereFun n x‖ = 1 := by
  let v : EuclideanSpace ℝ (Fin n) := x.val
  have hv : ‖v‖ ≤ 1 := by
    have hmem := x.property
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hrad : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith
  apply norm_eq_one_of_norm_sq_eq_one
  rw [diskSphereFun, norm_consLp_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  change (2 * ‖v‖ ^ 2 - 1) ^ 2 +
    (2 * √(1 - ‖v‖ ^ 2)) ^ 2 * ‖v‖ ^ 2 = 1
  nlinarith [Real.sq_sqrt hrad]

/-- The standard continuous quotient map from the ordinary closed `n`-disk to the metric
`n`-sphere. -/
noncomputable def closedDiskToSphere (n : ℕ) :
    C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, Sph n) where
  toFun x := ⟨diskSphereFun n x,
    mem_sphere_zero_iff_norm.mpr (norm_diskSphereFun n x)⟩
  continuous_toFun := by
    have hv : Continuous (fun x : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) 1 => (x.val : EuclideanSpace ℝ (Fin n))) :=
      continuous_subtype_val
    have hr : Continuous (fun x : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) 1 => ‖x.val‖) := hv.norm
    have hsqrt : Continuous (fun x : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) 1 => √(1 - ‖x.val‖ ^ 2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub (hr.pow 2))
    refine Continuous.subtype_mk (continuous_consLp.comp (Continuous.prodMk ?_ ?_)) _
    · exact (continuous_const.mul (hr.pow 2)).sub continuous_const
    · exact (continuous_const.mul hsqrt).smul hv

/-- Every boundary point of the ordinary disk is sent to the benchmark's first-coordinate
basepoint. -/
theorem closedDiskToSphere_boundary (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (hx : ‖x.val‖ = 1) :
    closedDiskToSphere n x = sphereBasepoint n := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  induction i using Fin.cases with
  | zero => norm_num [closedDiskToSphere, diskSphereFun, hx, sphereBasepoint]
  | succ i => simp [closedDiskToSphere, diskSphereFun, hx, sphereBasepoint]

/-- In every positive dimension, the disk-to-sphere quotient map is surjective. -/
theorem closedDiskToSphere_surjective (n : ℕ) :
    Function.Surjective (closedDiskToSphere (n + 1)) := by
  intro z
  let a : ℝ := z.val 0
  let w : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 fun i : Fin (n + 1) => z.val i.succ
  have hnorm : a ^ 2 + ‖w‖ ^ 2 = 1 := sphere_first_tail_norm_sq z
  have ha_sq : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖w‖]
  have habs : |a| ≤ 1 := (sq_le_one_iff_abs_le_one a).mp ha_sq
  have ha_lower : -1 ≤ a := (abs_le.mp habs).1
  have ha_upper : a ≤ 1 := (abs_le.mp habs).2
  by_cases ha : a = 1
  · have hw_norm : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    have hw : w = 0 := norm_eq_zero.mp hw_norm
    have hzbase : z = sphereBasepoint (n + 1) := by
      apply Subtype.ext
      rw [eq_consLp z.val]
      apply PiLp.ext
      intro i
      induction i using Fin.cases with
      | zero => simp [a, ha, sphereBasepoint]
      | succ i => simp [w, hw, sphereBasepoint]
    let v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
    have hv : ‖v‖ = 1 := by simp [v]
    let x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
      ⟨v, by rw [Metric.mem_closedBall, dist_zero_right, hv]⟩
    refine ⟨x, ?_⟩
    rw [closedDiskToSphere_boundary (n + 1) x hv, hzbase]
  · have halt : a < 1 := lt_of_le_of_ne ha_upper ha
    let r2 : ℝ := (a + 1) / 2
    let s2 : ℝ := 1 - r2
    let c : ℝ := 2 * √s2
    have hr2_nonneg : 0 ≤ r2 := by dsimp [r2]; linarith
    have hr2_le_one : r2 ≤ 1 := by dsimp [r2]; linarith
    have hs2_pos : 0 < s2 := by dsimp [s2, r2]; linarith
    have hc_pos : 0 < c := mul_pos (by norm_num) (Real.sqrt_pos.2 hs2_pos)
    have hw_sq : ‖w‖ ^ 2 = 1 - a ^ 2 := by nlinarith
    have hc_sq : c ^ 2 = 4 * s2 := by
      dsimp [c]
      rw [mul_pow, Real.sq_sqrt hs2_pos.le]
      ring
    let v : EuclideanSpace ℝ (Fin (n + 1)) := c⁻¹ • w
    have hv_sq : ‖v‖ ^ 2 = r2 := by
      rw [show ‖v‖ = c⁻¹ * ‖w‖ by
        unfold v
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc_pos)]]
      field_simp [hc_pos.ne']
      dsimp [r2, s2] at hc_sq ⊢
      nlinarith
    have hv_le : ‖v‖ ≤ 1 :=
      (sq_le_one_iff₀ (norm_nonneg v)).mp (hv_sq.trans_le hr2_le_one)
    let x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
      ⟨v, by rw [Metric.mem_closedBall, dist_zero_right]; exact hv_le⟩
    have hfirst : 2 * ‖v‖ ^ 2 - 1 = a := by
      rw [hv_sq]
      dsimp [r2]
      ring
    have htail : (2 * √(1 - ‖v‖ ^ 2) : ℝ) • v = w := by
      rw [hv_sq]
      change c • v = w
      rw [show v = c⁻¹ • w by rfl, smul_smul, mul_inv_cancel₀ hc_pos.ne', one_smul]
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change diskSphereFun (n + 1) x = z.val
    rw [eq_consLp z.val]
    change consLp (2 * ‖v‖ ^ 2 - 1) ((2 * √(1 - ‖v‖ ^ 2) : ℝ) • v) =
      consLp a w
    rw [hfirst, htail]

/-- The only nontrivial fibres of the disk-to-sphere map are on the collapsed boundary. -/
theorem closedDiskToSphere_eq_iff (n : ℕ)
    (x y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    closedDiskToSphere n x = closedDiskToSphere n y ↔
      x = y ∨ (‖x.val‖ = 1 ∧ ‖y.val‖ = 1) := by
  constructor
  · intro h
    have hvec : diskSphereFun n x = diskSphereFun n y := congrArg Subtype.val h
    have hfirst := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z 0) hvec
    have hsq : ‖x.val‖ ^ 2 = ‖y.val‖ ^ 2 := by
      simpa [diskSphereFun] using (show
        2 * ‖x.val‖ ^ 2 - 1 = 2 * ‖y.val‖ ^ 2 - 1 from hfirst)
    have hnorm : ‖x.val‖ = ‖y.val‖ :=
      eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _) hsq
    by_cases hx : ‖x.val‖ = 1
    · exact Or.inr ⟨hx, hnorm ▸ hx⟩
    · left
      apply Subtype.ext
      apply PiLp.ext
      intro i
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i.succ) hvec
      have hxle : ‖x.val‖ ≤ 1 := by
        have hmem := x.property
        rw [Metric.mem_closedBall, dist_zero_right] at hmem
        exact hmem
      have hxlt : ‖x.val‖ < 1 := lt_of_le_of_ne hxle hx
      have hrad : 0 < 1 - ‖x.val‖ ^ 2 := by nlinarith [norm_nonneg x.val]
      have hc : (2 * √(1 - ‖x.val‖ ^ 2) : ℝ) ≠ 0 :=
        (mul_pos (by norm_num) (Real.sqrt_pos.2 hrad)).ne'
      simp only [diskSphereFun, consLp_succ, PiLp.smul_apply, smul_eq_mul] at hi
      rw [← hnorm] at hi
      exact mul_left_cancel₀ hc hi
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [closedDiskToSphere_boundary n x hx, closedDiskToSphere_boundary n y hy]


end BanachIsometric.SphereGenerator
