import BanachIsometric.PiolaIdentity
import BanachIsometric.PiolaBlockCofactor
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Actual time-slice Jacobians of a zero-coordinate homotopy lift

Both maps are the genuine coordinate maps `F(z)=(H(z),0)` and
`h_t(x)=H(x,t)`. Their actual derivatives are related by the affine insertion
chain rule. The last corner of the actual adjugate is the spatial Jacobian
determinant on the time slice.
-/

namespace BanachIsometric

noncomputable section

def piolaSnocZeroLinear (n : ℕ) : PiolaSpace n →L[ℝ] PiolaSpace (n + 1) :=
  ContinuousLinearMap.pi (Fin.snoc (fun i : Fin n ↦ ContinuousLinearMap.proj i) 0)

@[simp]
theorem piolaSnocZeroLinear_apply {n : ℕ} (v : PiolaSpace n) :
    piolaSnocZeroLinear n v = Fin.snoc v 0 := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [piolaSnocZeroLinear]
  · simp [piolaSnocZeroLinear]

@[simp]
theorem piolaSnocZeroLinear_basis {n : ℕ} (j : Fin n) :
    piolaSnocZeroLinear n (piolaBasisVector j) = piolaBasisVector j.castSucc := by
  ext i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simp [piolaSnocZeroLinear_apply, piolaBasisVector]
  · simp [piolaSnocZeroLinear_apply, piolaBasisVector, Pi.single_apply]

@[simp]
theorem snoc_piolaBasisVector {n : ℕ} (j : Fin n) :
    Fin.snoc (piolaBasisVector j) 0 = piolaBasisVector j.castSucc :=
  (piolaSnocZeroLinear_apply (piolaBasisVector j)).symm.trans (piolaSnocZeroLinear_basis j)

def piolaHomotopyExtension {n : ℕ} (H : PiolaSpace (n + 1) → PiolaSpace n)
    (z : PiolaSpace (n + 1)) : PiolaSpace (n + 1) := Fin.snoc (H z) 0

def piolaTimeSlice {n : ℕ} (H : PiolaSpace (n + 1) → PiolaSpace n)
    (t : ℝ) (x : PiolaSpace n) : PiolaSpace n := H (Fin.snoc x t)

theorem hasFDerivAt_piolaTimeInsert {n : ℕ} (t : ℝ) (x : PiolaSpace n) :
    HasFDerivAt (fun z : PiolaSpace n ↦ Fin.snoc z t) (piolaSnocZeroLinear n) x := by
  apply hasFDerivAt_pi''
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · have hlast : (ContinuousLinearMap.proj (Fin.last n)).comp (piolaSnocZeroLinear n) = 0 := by
      ext v
      simp
    simpa only [Fin.snoc_last, hlast] using hasFDerivAt_const t x
  · have hproj : (ContinuousLinearMap.proj j.castSucc).comp (piolaSnocZeroLinear n) =
        (ContinuousLinearMap.proj j : PiolaSpace n →L[ℝ] ℝ) := by
      ext v
      simp
    simpa only [Fin.snoc_castSucc, hproj] using
      (ContinuousLinearMap.proj j : PiolaSpace n →L[ℝ] ℝ).hasFDerivAt

theorem contDiff_piolaHomotopyExtension {n : ℕ} {H : PiolaSpace (n + 1) → PiolaSpace n}
    (hH : ContDiff ℝ 2 H) : ContDiff ℝ 2 (piolaHomotopyExtension H) := by
  simpa only [Function.comp_def, piolaSnocZeroLinear_apply, piolaHomotopyExtension] using
    (piolaSnocZeroLinear n).contDiff.comp hH

theorem adjugate_piolaHomotopyExtension_timeSlice {n : ℕ}
    (H : PiolaSpace (n + 1) → PiolaSpace n) (x : PiolaSpace n) (t : ℝ)
    (hH : DifferentiableAt ℝ H (Fin.snoc x t)) :
    (piolaJacobian (piolaHomotopyExtension H) (Fin.snoc x t)).adjugate
      (Fin.last n) (Fin.last n) = (fderiv ℝ (piolaTimeSlice H t) x).det := by
  have hExt : HasFDerivAt (piolaHomotopyExtension H)
      ((piolaSnocZeroLinear n).comp (fderiv ℝ H (Fin.snoc x t))) (Fin.snoc x t) := by
    have hI : HasFDerivAt (piolaSnocZeroLinear n) (piolaSnocZeroLinear n) (H (Fin.snoc x t)) :=
      (piolaSnocZeroLinear n).hasFDerivAt
    simpa only [Function.comp_def, piolaSnocZeroLinear_apply, piolaHomotopyExtension] using
      hI.comp (Fin.snoc x t : PiolaSpace (n + 1)) hH.hasFDerivAt
  have hSlice : HasFDerivAt (piolaTimeSlice H t)
      ((fderiv ℝ H (Fin.snoc x t)).comp (piolaSnocZeroLinear n)) x :=
    hH.hasFDerivAt.comp x (hasFDerivAt_piolaTimeInsert (n := n) t x)
  have hminor : (piolaJacobian (piolaHomotopyExtension H) (Fin.snoc x t)).submatrix
      Fin.castSucc Fin.castSucc = piolaJacobian (piolaTimeSlice H t) x := by
    ext i j
    change fderiv ℝ (piolaHomotopyExtension H) (Fin.snoc x t)
      (piolaBasisVector j.castSucc) i.castSucc =
      fderiv ℝ (piolaTimeSlice H t) x (piolaBasisVector j) i
    rw [hExt.fderiv, hSlice.fderiv]
    simp only [ContinuousLinearMap.comp_apply, piolaSnocZeroLinear_apply,
      Fin.snoc_castSucc, snoc_piolaBasisVector]
  have hsign : (-1 : ℝ) ^ (n + n) = 1 := by
    calc
      (-1 : ℝ) ^ (n + n) = ((-1 : ℝ) * (-1)) ^ n := by rw [pow_add, mul_pow]
      _ = 1 := by simp
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_last, Fin.succAbove_last, hminor, det_piolaJacobian, hsign, one_mul]

end

end BanachIsometric
