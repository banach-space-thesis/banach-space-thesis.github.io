import ThesisCommon.Analysis.MatrixUnitSumNorms
import ThesisCommon.Analysis.MatrixHilbertSchmidtBounds

/-! Entry bounds in the genuine finite lp operator norm. These estimates
are used after finite Ramsey selection; no matrix norm is replaced. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem matrixEntry_norm_le (p : BanachExponent) {N : ℕ}
    (A : FiniteMatrixBlock 𝕜 p N) (i j : Fin N) :
    ‖matrixEntry p i j A‖ ≤ ‖A‖ := by
  exact (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le p.property))
    (A (lp.single p.val j (1 : 𝕜))) i).trans
    (by simpa only [lp.norm_single (zero_lt_one.trans_le p.property), norm_one, mul_one]
      using A.le_opNorm (lp.single p.val j (1 : 𝕜)))

theorem finiteMatrix_eq_sum_matrixUnits (p : BanachExponent) {N : ℕ}
    (A : FiniteMatrixBlock 𝕜 p N) :
    A = ∑ i : Fin N, ∑ j : Fin N, matrixEntry p i j A • matrixUnit p i j := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  rw [finiteMatrix_apply_eq_sum]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    matrixUnit_apply, smul_eq_mul]
  simp [mul_comm]

theorem finiteMatrix_norm_le_of_entries_le (p : BanachExponent)
    (hp : 1 < p.val.toReal) {N : ℕ} (hN : 0 < N)
    (A : FiniteMatrixBlock 𝕜 p N) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, ‖matrixEntry p i j A‖ ≤ C) : ‖A‖ ≤ N * C := by
  classical
  let v : FiniteLpSpace 𝕜 p N := ∑ i : Fin N, lp.single p.val i (1 : 𝕜)
  have hv (i : Fin N) : v i = 1 := by simp [v, lp.single_apply, Pi.single_apply]
  have hvnorm : ‖v‖ = (N : ℝ) ^ (1 / p.val.toReal) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      norm_lp_unimodular_sum_single (𝕜 := 𝕜) p.val (zero_lt_one.trans hp)
        (Finset.univ : Finset (Fin N)) (fun _ => 1) (fun _ _ => norm_one)
  have hpq : p.val.toReal.HolderConjugate (p.val.toReal / (p.val.toReal - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hpow : (N : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) *
      (N : ℝ) ^ (1 / p.val.toReal) = N := by
    rw [← Real.rpow_add (Nat.cast_pos.mpr hN), one_div, one_div,
      hpq.symm.inv_add_inv_eq_one, Real.rpow_one]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg N) hC)
  intro x
  have hsum := finite_lp_sum_norm_bound (𝕜 := 𝕜) p hp Finset.univ x
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hrow (i : Fin N) : ‖A x i‖ ≤ C * ∑ j : Fin N, ‖x j‖ := by
    rw [finiteMatrix_apply_eq_sum, Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
  have hbound := lp_norm_le_mul_of_pointwise v (A x)
    (mul_nonneg hC (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    (fun i => by simpa only [hv, norm_one, mul_one] using hrow i)
  calc
    ‖A x‖ ≤ (C * ∑ j : Fin N, ‖x j‖) * ‖v‖ := hbound
    _ ≤ (C * ((N : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) * ‖x‖)) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hC) (norm_nonneg _)
    _ = C * ‖x‖ * ((N : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) *
        (N : ℝ) ^ (1 / p.val.toReal)) := by rw [hvnorm]; ring
    _ = (N * C) * ‖x‖ := by rw [hpow]; ring

theorem matrixOperator_norm_le_of_coefficients_le (p : BanachExponent)
    (hp : 1 < p.val.toReal) {N : ℕ} (hN : 0 < N)
    (S : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N)
    {C : ℝ} (hC : 0 ≤ C)
    (hS : ∀ i j k l, ‖matrixEntry p i j (S (matrixUnit p k l))‖ ≤ C) :
    ‖S‖ ≤ (N : ℝ) ^ 3 * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) hC)
  intro A
  have hentry (i j : Fin N) :
      ‖matrixEntry p i j (S A)‖ ≤ (N : ℝ) ^ 2 * C * ‖A‖ := by
    have heq : matrixEntry p i j (S A) = ∑ k : Fin N, ∑ l : Fin N,
        matrixEntry p k l A * matrixEntry p i j (S (matrixUnit p k l)) := by
      conv_lhs => rw [finiteMatrix_eq_sum_matrixUnits p A]
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [heq]
    calc
      _ ≤ ∑ k : Fin N, ∑ l : Fin N,
          ‖matrixEntry p k l A * matrixEntry p i j (S (matrixUnit p k l))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
      _ ≤ ∑ _k : Fin N, ∑ _l : Fin N, ‖A‖ * C := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro l _
        rw [norm_mul]
        exact mul_le_mul (matrixEntry_norm_le p A k l) (hS i j k l)
          (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp; ring
  calc
    ‖S A‖ ≤ N * ((N : ℝ) ^ 2 * C * ‖A‖) :=
      finiteMatrix_norm_le_of_entries_le p hp hN (S A)
        (mul_nonneg (mul_nonneg (sq_nonneg _) hC) (norm_nonneg _)) hentry
    _ = _ := by ring

end ThesisCommon
