import BanachIsometric.PiolaIdentity
import BanachIsometric.PiolaCofactorExpansion

/-!
# Differentiating the actual cofactor flux

The finite product and permutation sums below are the concrete cofactor
expression. Their derivatives are computed from the actual second Fréchet
derivative. Symmetry and the proved permutation cancellation give zero
divergence.
-/

namespace BanachIsometric

open scoped BigOperators Classical

noncomputable def piolaProduct {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) (x : PiolaSpace n) : ℝ :=
  ∏ k ∈ Finset.univ.erase j, piolaJacobian F x k (σ k)

noncomputable def piolaProductDerivative {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (x : PiolaSpace n) (j : Fin n) (σ : Equiv.Perm (Fin n)) : PiolaSpace n →L[ℝ] ℝ :=
  ∑ k ∈ Finset.univ.erase j,
    (∏ l ∈ (Finset.univ.erase j).erase k, piolaJacobian F x l (σ l)) •
      piolaJacobianEntryDerivative F x k (σ k)

theorem hasFDerivAt_piolaProduct {n : ℕ} {F : PiolaSpace n → PiolaSpace n}
    (hF : ContDiff ℝ 2 F) (x : PiolaSpace n) (j : Fin n) (σ : Equiv.Perm (Fin n)) :
    HasFDerivAt (piolaProduct F j σ) (piolaProductDerivative F x j σ) x := by
  simpa only [piolaProduct, piolaProductDerivative, Finset.prod_apply] using
    HasFDerivAt.finset_prod (fun k (_hk : k ∈ Finset.univ.erase j) =>
      hasFDerivAt_piolaJacobian_entry hF x k (σ k))

theorem piolaProductDerivative_apply_basis {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (x : PiolaSpace n) (j a : Fin n) (σ : Equiv.Perm (Fin n)) :
    piolaProductDerivative F x j σ (piolaBasisVector a) =
      ∑ k ∈ Finset.univ.erase j,
        (∏ l ∈ (Finset.univ.erase j).erase k, piolaJacobian F x l (σ l)) *
          piolaHessian F x k a (σ k) := by
  simp only [piolaProductDerivative, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, piolaJacobianEntryDerivative_apply_basis]

noncomputable def piolaCofactor {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (j i : Fin n) (x : PiolaSpace n) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    if σ j = i then ((Equiv.Perm.sign σ : ℤ) : ℝ) * piolaProduct F j σ x else 0

noncomputable def piolaCofactorDerivative {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (x : PiolaSpace n) (j i : Fin n) : PiolaSpace n →L[ℝ] ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    if σ j = i then ((Equiv.Perm.sign σ : ℤ) : ℝ) • piolaProductDerivative F x j σ else 0

theorem hasFDerivAt_piolaCofactor {n : ℕ} {F : PiolaSpace n → PiolaSpace n}
    (hF : ContDiff ℝ 2 F) (x : PiolaSpace n) (j i : Fin n) :
    HasFDerivAt (piolaCofactor F j i) (piolaCofactorDerivative F x j i) x := by
  unfold piolaCofactor piolaCofactorDerivative
  apply HasFDerivAt.fun_sum
  intro σ _
  by_cases h : σ j = i
  · simpa only [if_pos h, smul_eq_mul] using
      (hasFDerivAt_piolaProduct hF x j σ).const_smul (((Equiv.Perm.sign σ : ℤ) : ℝ))
  · simpa only [if_neg h] using (hasFDerivAt_const (0 : ℝ) x)

theorem piolaCofactorDerivative_apply_basis {n : ℕ}
    (F : PiolaSpace n → PiolaSpace n) (x : PiolaSpace n) (j i a : Fin n) :
    piolaCofactorDerivative F x j i (piolaBasisVector a) =
      ∑ σ : Equiv.Perm (Fin n), if σ j = i then
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * piolaProductDerivative F x j σ (piolaBasisVector a)
      else 0 := by
  simp only [piolaCofactorDerivative, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : σ j = i <;> simp [h]

theorem sum_piolaCofactorDerivative_basis_eq_zero {n : ℕ}
    {F : PiolaSpace n → PiolaSpace n} (hF : ContDiff ℝ 2 F)
    (x : PiolaSpace n) (j : Fin n) :
    (∑ i : Fin n, piolaCofactorDerivative F x j i (piolaBasisVector i)) = 0 := by
  calc
    (∑ i : Fin n, piolaCofactorDerivative F x j i (piolaBasisVector i)) =
        ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            piolaProductDerivative F x j σ (piolaBasisVector (σ j)) := by
      simp_rw [piolaCofactorDerivative_apply_basis]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      simp
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ k ∈ Finset.univ.erase j,
        piolaMixedTerm (piolaJacobian F x) (piolaHessian F x) j k σ := by
      simp_rw [piolaProductDerivative_apply_basis, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro k _
      unfold piolaMixedTerm
      ring
    _ = ∑ k ∈ Finset.univ.erase j, ∑ σ : Equiv.Perm (Fin n),
        piolaMixedTerm (piolaJacobian F x) (piolaHessian F x) j k σ := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact piola_mixed_permutation_sum_zero (piolaJacobian F x) (piolaHessian F x)
        (piolaHessian_symm hF x) (Finset.mem_erase.mp hk).1.symm

theorem piolaCofactor_eq_adjugate {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (j i : Fin n) (x : PiolaSpace n) :
    piolaCofactor F j i x = (piolaJacobian F x).adjugate i j := by
  unfold piolaCofactor piolaProduct
  exact (adjugate_apply_eq_sum_permutations_erase (piolaJacobian F x) i j).symm

theorem hasFDerivAt_adjugate_piolaJacobian_entry {n : ℕ}
    {F : PiolaSpace n → PiolaSpace n} (hF : ContDiff ℝ 2 F)
    (x : PiolaSpace n) (j i : Fin n) :
    HasFDerivAt (fun z => (piolaJacobian F z).adjugate i j)
      (piolaCofactorDerivative F x j i) x := by
  have hfun : (fun z => (piolaJacobian F z).adjugate i j) = piolaCofactor F j i := by
    funext z
    exact (piolaCofactor_eq_adjugate F j i z).symm
  rw [hfun]
  exact hasFDerivAt_piolaCofactor hF x j i

/-- The actual Piola identity for the Jacobian of a C² map in arbitrary finite
real coordinate dimension. No divergence equation is a hypothesis. -/
theorem piola_identity {n : ℕ} {F : PiolaSpace n → PiolaSpace n}
    (hF : ContDiff ℝ 2 F) (x : PiolaSpace n) (j : Fin n) :
    (∑ i : Fin n, fderiv ℝ (fun z => (piolaJacobian F z).adjugate i j) x
      (piolaBasisVector i)) = 0 := by
  have hderiv (i : Fin n) :
      fderiv ℝ (fun z => (piolaJacobian F z).adjugate i j) x =
        piolaCofactorDerivative F x j i :=
    (hasFDerivAt_adjugate_piolaJacobian_entry hF x j i).fderiv
  simp_rw [hderiv]
  exact sum_piolaCofactorDerivative_basis_eq_zero hF x j

end BanachIsometric
