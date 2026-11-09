import BanachIsometric.PiolaDifferential

/-!
# Weighted Piola flux and its actual divergence

Multiplying a cofactor column by a target test function converts its divergence
into the signed Jacobian times one target-coordinate derivative. This is the
local differential identity needed for homotopy invariance by box divergence.
-/

namespace BanachIsometric

open scoped BigOperators Classical

noncomputable def weightedPiolaFlux {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (g : PiolaSpace n → ℝ) (j : Fin n) (x : PiolaSpace n) : PiolaSpace n :=
  fun i => (piolaJacobian F x).adjugate i j * g (F x)

noncomputable def weightedPiolaFluxDerivative {n : ℕ}
    (F : PiolaSpace n → PiolaSpace n) (g : PiolaSpace n → ℝ)
    (x : PiolaSpace n) (j : Fin n) : PiolaSpace n →L[ℝ] PiolaSpace n :=
  ContinuousLinearMap.pi (fun i =>
    (piolaJacobian F x).adjugate i j • ((fderiv ℝ g (F x)).comp (fderiv ℝ F x)) +
      g (F x) • piolaCofactorDerivative F x j i)

theorem hasFDerivAt_weightedPiolaFlux {n : ℕ} {F : PiolaSpace n → PiolaSpace n}
    (hF : ContDiff ℝ 2 F) {g : PiolaSpace n → ℝ} (x : PiolaSpace n)
    (hg : DifferentiableAt ℝ g (F x)) (j : Fin n) :
    HasFDerivAt (weightedPiolaFlux F g j) (weightedPiolaFluxDerivative F g x j) x := by
  have hcomp := hg.hasFDerivAt.comp x ((hF.differentiable (by norm_num)) x).hasFDerivAt
  unfold weightedPiolaFlux weightedPiolaFluxDerivative
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hasFDerivAt_adjugate_piolaJacobian_entry hF x j i).fun_mul hcomp

theorem piola_adjugate_chain_sum {n : ℕ} (F : PiolaSpace n → PiolaSpace n)
    (x : PiolaSpace n) (L : PiolaSpace n →L[ℝ] ℝ) (j : Fin n) :
    (∑ i : Fin n, (piolaJacobian F x).adjugate i j *
      L (fderiv ℝ F x (piolaBasisVector i))) =
      (fderiv ℝ F x).det * L (piolaBasisVector j) := by
  let A := piolaJacobian F x
  let T := fderiv ℝ F x
  have hcol : (∑ i : Fin n, A.adjugate i j • piolaBasisVector i) =
      A.adjugate.mulVec (piolaBasisVector j) := by
    simpa only [piolaBasisVector, Matrix.mulVec_single_one,
      Pi.basisFun_repr, Pi.basisFun_apply] using
      (Pi.basisFun ℝ (Fin n)).sum_repr (fun i => A.adjugate i j)
  have hJ (v : PiolaSpace n) : A.mulVec v = T v := by
    change (piolaJacobian F x).mulVec v = fderiv ℝ F x v
    rw [piolaJacobian_eq_toMatrix]
    exact LinearMap.toMatrix'_mulVec _ _
  have hvec : (∑ i : Fin n, A.adjugate i j • T (piolaBasisVector i)) =
      A.det • piolaBasisVector j := by
    calc
      (∑ i : Fin n, A.adjugate i j • T (piolaBasisVector i)) =
          T (∑ i : Fin n, A.adjugate i j • piolaBasisVector i) := by
        simp only [map_sum, map_smul]
      _ = T (A.adjugate.mulVec (piolaBasisVector j)) := congrArg T hcol
      _ = A.mulVec (A.adjugate.mulVec (piolaBasisVector j)) := (hJ _).symm
      _ = (A * A.adjugate).mulVec (piolaBasisVector j) := Matrix.mulVec_mulVec _ _ _
      _ = A.det • piolaBasisVector j := by
        rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  calc
    (∑ i : Fin n, A.adjugate i j * L (T (piolaBasisVector i))) =
        L (∑ i : Fin n, A.adjugate i j • T (piolaBasisVector i)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = A.det * L (piolaBasisVector j) := by rw [hvec, map_smul, smul_eq_mul]
    _ = (fderiv ℝ F x).det * L (piolaBasisVector j) := by
      rw [show A.det = (fderiv ℝ F x).det from det_piolaJacobian F x]

noncomputable def coordinateDivergence {n : ℕ} (V : PiolaSpace n → PiolaSpace n)
    (x : PiolaSpace n) : ℝ :=
  ∑ i : Fin n, fderiv ℝ V x (piolaBasisVector i) i

/-- The weighted Piola divergence identity for actual derivatives. -/
theorem weighted_piola_divergence {n : ℕ} {F : PiolaSpace n → PiolaSpace n}
    (hF : ContDiff ℝ 2 F) {g : PiolaSpace n → ℝ} (x : PiolaSpace n)
    (hg : DifferentiableAt ℝ g (F x)) (j : Fin n) :
    coordinateDivergence (weightedPiolaFlux F g j) x =
      (fderiv ℝ F x).det * fderiv ℝ g (F x) (piolaBasisVector j) := by
  unfold coordinateDivergence
  rw [(hasFDerivAt_weightedPiolaFlux hF x hg j).fderiv]
  simp only [weightedPiolaFluxDerivative, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_piolaCofactorDerivative_basis_eq_zero hF x j, mul_zero, add_zero]
  exact piola_adjugate_chain_sum F x (fderiv ℝ g (F x)) j

end BanachIsometric
