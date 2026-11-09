import BanachIsometric.SphereGenerator
import BanachIsometric.PiolaIdentity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual derivative of the disk-to-sphere cone chart on the first axis

Source and target coordinates retain their ordinary Pi norms. The disk tail
uses its genuine Euclidean norm. The actual chart is the radial cone on the
literal disk quotient formula, in the order `[radius, disk coordinates]`.
-/

namespace BanachIsometric.SphereGenerator

open scoped NNReal Topology

noncomputable section

def diskSphereConeTail (n : ℕ) : PiolaSpace (n + 2) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (euclideanCoordinates (n + 1)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin (n + 1) => ContinuousLinearMap.proj i.succ))

@[simp]
theorem diskSphereConeTail_apply (n : ℕ) (z : PiolaSpace (n + 2)) (i : Fin (n + 1)) :
    diskSphereConeTail n z i = z i.succ := rfl

def diskSphereConeAxis (n : ℕ) (ρ r : ℝ) : PiolaSpace (n + 2) := Fin.cons ρ (Fin.cons r 0)

theorem diskSphereConeTail_axis (n : ℕ) (ρ r : ℝ) :
    diskSphereConeTail n (diskSphereConeAxis n ρ r) = EuclideanSpace.single 0 r := by
  ext i
  induction i using Fin.cases with
  | zero => simp [diskSphereConeAxis]
  | succ i => simp [diskSphereConeAxis, EuclideanSpace.single_apply]

@[simp]
theorem norm_sq_diskSphereConeTail_axis (n : ℕ) (ρ r : ℝ) :
    ‖diskSphereConeTail n (diskSphereConeAxis n ρ r)‖ ^ 2 = r ^ 2 := by
  rw [diskSphereConeTail_axis, EuclideanSpace.norm_single, Real.norm_eq_abs, sq_abs]

def diskSphereConeChart (n : ℕ) (z : PiolaSpace (n + 2)) : PiolaSpace (n + 2) :=
  Fin.cons (z 0 * (2 * ‖diskSphereConeTail n z‖ ^ 2 - 1))
    (fun i : Fin (n + 1) => 2 * z 0 * Real.sqrt (1 - ‖diskSphereConeTail n z‖ ^ 2) * z i.succ)

/-- This is exactly the radial cone on the paper's actual disk quotient. -/
theorem diskSphereConeChart_eq_raw (n : ℕ) (z : PiolaSpace (n + 2)) :
    diskSphereConeChart n z = WithLp.ofLp
      (z 0 • consLp (2 * ‖diskSphereConeTail n z‖ ^ 2 - 1)
        ((2 * Real.sqrt (1 - ‖diskSphereConeTail n z‖ ^ 2) : ℝ) • diskSphereConeTail n z)) := by
  ext i
  induction i using Fin.cases with
  | zero => simp [diskSphereConeChart, PiLp.smul_apply, smul_eq_mul]
  | succ i =>
      change 2 * z 0 * Real.sqrt (1 - ‖diskSphereConeTail n z‖ ^ 2) * z i.succ =
        z 0 * ((2 * Real.sqrt (1 - ‖diskSphereConeTail n z‖ ^ 2)) * diskSphereConeTail n z i)
      rw [diskSphereConeTail_apply]
      ring

def diskSphereConeChartDerivative (n : ℕ) (ρ r : ℝ) :
    PiolaSpace (n + 2) →L[ℝ] PiolaSpace (n + 2) :=
  let s := Real.sqrt (1 - r ^ 2)
  let p₀ : PiolaSpace (n + 2) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let p₁ : PiolaSpace (n + 2) →L[ℝ] ℝ := ContinuousLinearMap.proj (0 : Fin (n + 1)).succ
  ContinuousLinearMap.pi (Fin.cons
    ((2 * r ^ 2 - 1) • p₀ + (4 * ρ * r) • p₁)
    (Fin.cons ((2 * s * r) • p₀ + (2 * ρ * s - 2 * ρ * r ^ 2 / s) • p₁)
      (fun j : Fin n => (2 * ρ * s) • (ContinuousLinearMap.proj j.succ.succ))))

theorem hasFDerivAt_norm_sq_diskSphereConeTail_axis (n : ℕ) (ρ r : ℝ) :
    HasFDerivAt (fun z => ‖diskSphereConeTail n z‖ ^ 2)
      ((2 * r) • (ContinuousLinearMap.proj (0 : Fin (n + 1)).succ : PiolaSpace (n + 2) →L[ℝ] ℝ))
      (diskSphereConeAxis n ρ r) := by
  have ht : HasFDerivAt (diskSphereConeTail n) (diskSphereConeTail n) (diskSphereConeAxis n ρ r) :=
    (diskSphereConeTail n).hasFDerivAt
  have hD : 2 • (innerSL ℝ (diskSphereConeTail n (diskSphereConeAxis n ρ r))).comp (diskSphereConeTail n) =
      (2 * r) • (ContinuousLinearMap.proj (0 : Fin (n + 1)).succ : PiolaSpace (n + 2) →L[ℝ] ℝ) := by
    ext w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_coe,
      diskSphereConeTail_axis, EuclideanSpace.inner_single_left, diskSphereConeTail_apply,
      starRingEnd_apply, star_trivial, smul_eq_mul, ContinuousLinearMap.proj_apply]
    ring
  rw [← hD]
  exact ht.norm_sq

theorem hasFDerivAt_diskSphereConeChart_axis (n : ℕ) (ρ r : ℝ) (hr : r ^ 2 < 1) :
    HasFDerivAt (diskSphereConeChart n) (diskSphereConeChartDerivative n ρ r)
      (diskSphereConeAxis n ρ r) := by
  let p := diskSphereConeAxis n ρ r
  let s := Real.sqrt (1 - r ^ 2)
  let p₀ : PiolaSpace (n + 2) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let p₁ : PiolaSpace (n + 2) →L[ℝ] ℝ := ContinuousLinearMap.proj (0 : Fin (n + 1)).succ
  have hp₀ : p 0 = ρ := rfl
  have hp₁ : p (1 : Fin (n + 2)) = r := rfl
  have hpTail (j : Fin n) : p j.succ.succ = 0 := rfl
  have hnormP : ‖diskSphereConeTail n p‖ ^ 2 = r ^ 2 := norm_sq_diskSphereConeTail_axis n ρ r
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hr)).ne'
  have h₀ : HasFDerivAt (fun z : PiolaSpace (n + 2) => z 0) p₀ p := p₀.hasFDerivAt
  have hq := hasFDerivAt_norm_sq_diskSphereConeTail_axis n ρ r
  have hqs : HasFDerivAt (fun z => 1 - ‖diskSphereConeTail n z‖ ^ 2) (-((2 * r) • p₁)) p := by
    simpa only [zero_sub] using (hasFDerivAt_const (1 : ℝ) p).sub hq
  have hroot : HasFDerivAt (fun z => Real.sqrt (1 - ‖diskSphereConeTail n z‖ ^ 2))
      ((1 / (2 * s)) • (-((2 * r) • p₁))) p := by
    simpa only [hnormP] using hqs.sqrt
      (by rw [hnormP]; exact (sub_pos.mpr hr).ne')
  apply hasFDerivAt_pi''
  intro i
  induction i using Fin.cases with
  | zero =>
      convert h₀.mul ((hq.const_mul 2).sub_const 1) using 1
      ext w
      simp [diskSphereConeChartDerivative, p₀, hp₀, hnormP]
      ring
  | succ i =>
      have hi := ((h₀.mul hroot).const_mul 2).mul
        (ContinuousLinearMap.proj i.succ : PiolaSpace (n + 2) →L[ℝ] ℝ).hasFDerivAt
      convert hi using 1
      · funext z
        change 2 * z 0 * Real.sqrt (1 - ‖diskSphereConeTail n z‖ ^ 2) * z i.succ =
          2 * (z 0 * Real.sqrt (1 - ‖diskSphereConeTail n z‖ ^ 2)) * z i.succ
        ring
      · ext w
        induction i using Fin.cases with
        | zero =>
            simp [diskSphereConeChartDerivative, p₀, p₁, hp₀, hp₁, hnormP, s]
            dsimp [s] at hs
            field_simp [hs]
            ring
        | succ j =>
            simp [diskSphereConeChartDerivative, p₀, p₁, hp₀, hpTail, hnormP, s, mul_assoc]

end

end BanachIsometric.SphereGenerator
