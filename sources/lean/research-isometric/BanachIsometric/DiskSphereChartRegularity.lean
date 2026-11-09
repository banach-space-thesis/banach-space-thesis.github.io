import BanachIsometric.SphereGenerator
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Actual smooth local formulas for the disk quotient and its inverse away
from the collapsed boundary. These establish chart regularity without an
orientation or degree premise. -/

noncomputable section
namespace BanachIsometric.SphereGenerator
open Set Metric NormedSpace
open scoped Topology NNReal

def diskSphereAmbient (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  consLp (2 * ‖v‖ ^ 2 - 1) ((2 * Real.sqrt (1 - ‖v‖ ^ 2)) • v)

def sphereTail (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (euclideanCoordinates n).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (ContinuousLinearMap.proj i.succ).comp
      (euclideanCoordinates (n + 1)).toContinuousLinearMap))

@[simp] theorem sphereTail_consLp (n : ℕ) (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    sphereTail n (consLp a v) = v := by
  ext i
  rfl

def sphereDiskInverseAmbient (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  (2 * Real.sqrt ((1 - z 0) / 2))⁻¹ • sphereTail n z

theorem contDiff_consLp (n : ℕ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun p : ℝ × EuclideanSpace ℝ (Fin n) => consLp p.1 p.2) := by
  change ContDiff ℝ k (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
    (euclideanCoordinates (n + 1)).symm (Fin.cons p.1 (euclideanCoordinates n p.2)))
  apply (euclideanCoordinates (n + 1)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  induction i using Fin.cases with
  | zero => exact contDiff_fst
  | succ i => exact (contDiff_pi.mp ((euclideanCoordinates n).contDiff.comp contDiff_snd)) i

theorem contDiffAt_diskSphereAmbient (n : ℕ) (k : WithTop ℕ∞)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ < 1) :
    ContDiffAt ℝ k (diskSphereAmbient n) v := by
  have hq : ContDiffAt ℝ k (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) v :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hrad : 1 - ‖v‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg v]
  have hroot := (contDiffAt_const.sub hq).sqrt hrad
  exact (contDiff_consLp n k).contDiffAt.comp v
    (((contDiffAt_const.mul hq).sub contDiffAt_const).prodMk
      ((contDiffAt_const.mul hroot).smul contDiffAt_id))

theorem contDiffAt_sphereDiskInverseAmbient (n : ℕ) (k : WithTop ℕ∞)
    (z : EuclideanSpace ℝ (Fin (n + 1))) (hz : z 0 < 1) :
    ContDiffAt ℝ k (sphereDiskInverseAmbient n) z := by
  let a : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj 0).comp (euclideanCoordinates (n + 1)).toContinuousLinearMap
  have hq : ContDiffAt ℝ k (fun x => (1 - a x) / 2) z :=
    (contDiffAt_const.sub a.contDiff.contDiffAt).div_const 2
  have hpos : 0 < (1 - a z) / 2 := by change 0 < (1 - z 0) / 2; linarith
  have hroot := hq.sqrt hpos.ne'
  have hcoef : (2 : ℝ) * Real.sqrt ((1 - a z) / 2) ≠ 0 :=
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr hpos)).ne'
  exact ((contDiffAt_const.mul hroot).inv hcoef).smul (sphereTail n).contDiff.contDiffAt

theorem sphereDiskInverse_diskSphereAmbient (n : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ < 1) :
    sphereDiskInverseAmbient n (diskSphereAmbient n v) = v := by
  have hpos : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hc : (2 : ℝ) * Real.sqrt (1 - ‖v‖ ^ 2) ≠ 0 :=
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr hpos)).ne'
  simp only [sphereDiskInverseAmbient, diskSphereAmbient, consLp_zero, sphereTail_consLp]
  rw [show (1 - (2 * ‖v‖ ^ 2 - 1)) / 2 = 1 - ‖v‖ ^ 2 by ring,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem exists_lipschitzOn_diskSphereAmbient_nhds (n : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ < 1) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 v, LipschitzOnWith L (diskSphereAmbient n) U :=
  (contDiffAt_diskSphereAmbient n 1 v hv).exists_lipschitzOnWith

theorem exists_lipschitzOn_sphereDiskInverseAmbient_nhds (n : ℕ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) (hz : z 0 < 1) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z, LipschitzOnWith L (sphereDiskInverseAmbient n) U :=
  (contDiffAt_sphereDiskInverseAmbient n 1 z hz).exists_lipschitzOnWith

end BanachIsometric.SphereGenerator
