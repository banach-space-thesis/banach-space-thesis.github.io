import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-!
# Piola cancellation for actual Jacobians

The algebraic cancellation pairs a permutation with its right composition by
a transposition. Its determinant sign reverses, the product outside the two
indices stays fixed, and symmetry exchanges the two Hessian directions.
-/

namespace BanachIsometric

open scoped BigOperators

section Cancellation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def piolaMixedTerm (J : Matrix κ κ ℝ) (H : κ → κ → κ → ℝ)
    (j k : κ) (σ : Equiv.Perm κ) : ℝ :=
  ((Equiv.Perm.sign σ : ℤ) : ℝ) * H k (σ j) (σ k) *
    ∏ l ∈ (Finset.univ.erase j).erase k, J l (σ l)

/-- The two Hessian terms related by a transposition cancel exactly. -/
theorem piolaMixedTerm_swap (J : Matrix κ κ ℝ) (H : κ → κ → κ → ℝ)
    (hsym : ∀ r a b, H r a b = H r b a) {j k : κ} (hjk : j ≠ k)
    (σ : Equiv.Perm κ) :
    piolaMixedTerm J H j k (σ * Equiv.swap j k) = -piolaMixedTerm J H j k σ := by
  have hsign : ((Equiv.Perm.sign (σ * Equiv.swap j k) : ℤ) : ℝ) =
      -((Equiv.Perm.sign σ : ℤ) : ℝ) := by
    rw [map_mul, Equiv.Perm.sign_swap hjk]
    simp
  have hprod : (∏ l ∈ (Finset.univ.erase j).erase k, J l ((σ * Equiv.swap j k) l)) =
      ∏ l ∈ (Finset.univ.erase j).erase k, J l (σ l) := by
    apply Finset.prod_congr rfl
    intro l hl
    have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
    have hlj : l ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hlj hlk]
  dsimp only [piolaMixedTerm]
  rw [hsign, hprod]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hsym k (σ k) (σ j)]
  ring

/-- Every mixed-Hessian contribution to the Piola divergence sums to zero.
This is algebraic cancellation, with no divergence or degree premise. -/
theorem piola_mixed_permutation_sum_zero
    (J : Matrix κ κ ℝ) (H : κ → κ → κ → ℝ)
    (hsym : ∀ r a b, H r a b = H r b a) {j k : κ} (hjk : j ≠ k) :
    (∑ σ : Equiv.Perm κ, piolaMixedTerm J H j k σ) = 0 := by
  let S : ℝ := ∑ σ : Equiv.Perm κ, piolaMixedTerm J H j k σ
  have heq : S = -S := by
    calc
      S = ∑ σ : Equiv.Perm κ, piolaMixedTerm J H j k (σ * Equiv.swap j k) :=
        (Equiv.sum_comp (Equiv.mulRight (Equiv.swap j k)) (piolaMixedTerm J H j k)).symm
      _ = ∑ σ : Equiv.Perm κ, -piolaMixedTerm J H j k σ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact piolaMixedTerm_swap J H hsym hjk σ
      _ = -S := Finset.sum_neg_distrib _
  change S = 0
  linarith

end Cancellation

section ActualJacobian

abbrev PiolaSpace (n : ℕ) := Fin n → ℝ

def piolaBasisVector {n : ℕ} (i : Fin n) : PiolaSpace n := Pi.single i 1

/-- Output coordinates are rows and input directions are columns. -/
noncomputable def piolaJacobian {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (x : PiolaSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  fun k l => fderiv ℝ F x (piolaBasisVector l) k

theorem piolaJacobian_eq_toMatrix {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (x : PiolaSpace n) :
    piolaJacobian F x = LinearMap.toMatrix' (fderiv ℝ F x).toLinearMap := by
  ext k l
  rfl

theorem det_piolaJacobian {n : ℕ} (F : PiolaSpace n → PiolaSpace n) (x : PiolaSpace n) :
    (piolaJacobian F x).det = (fderiv ℝ F x).det := by
  rw [piolaJacobian_eq_toMatrix]
  exact LinearMap.det_toMatrix' _

noncomputable def piolaHessian {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (x : PiolaSpace n) (k a b : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ F) x (piolaBasisVector a) (piolaBasisVector b) k

theorem piolaHessian_symm {n : ℕ} {F : PiolaSpace n → PiolaSpace n}
    (hF : ContDiff ℝ 2 F) (x : PiolaSpace n) (k a b : Fin n) :
    piolaHessian F x k a b = piolaHessian F x k b a := by
  have hf : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdf : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact congrFun (second_derivative_symmetric (fun z => (hf z).hasFDerivAt)
    ((hdf.differentiable le_rfl) x).hasFDerivAt
    (piolaBasisVector a) (piolaBasisVector b)) k

noncomputable def piolaJacobianEntryDerivative {n : ℕ}
    (F : PiolaSpace n → PiolaSpace n) (x : PiolaSpace n) (k l : Fin n) :
    PiolaSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp
    ((fderiv ℝ (fderiv ℝ F) x).flip (piolaBasisVector l))

theorem hasFDerivAt_piolaJacobian_entry {n : ℕ} {F : PiolaSpace n → PiolaSpace n}
    (hF : ContDiff ℝ 2 F) (x : PiolaSpace n) (k l : Fin n) :
    HasFDerivAt (fun z => piolaJacobian F z k l)
      (piolaJacobianEntryDerivative F x k l) x := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hA := ((hdf.differentiable le_rfl) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const (piolaBasisVector l) x)
  have hproj := (ContinuousLinearMap.proj k : PiolaSpace n →L[ℝ] ℝ).hasFDerivAt.comp x hA
  simpa only [piolaJacobian, piolaJacobianEntryDerivative,
    ContinuousLinearMap.comp_zero, zero_add] using hproj

@[simp] theorem piolaJacobianEntryDerivative_apply_basis {n : ℕ}
    (F : PiolaSpace n → PiolaSpace n) (x : PiolaSpace n) (k l a : Fin n) :
    piolaJacobianEntryDerivative F x k l (piolaBasisVector a) = piolaHessian F x k a l := rfl

end ActualJacobian

end BanachIsometric
