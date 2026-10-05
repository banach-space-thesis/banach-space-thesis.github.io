import ThesisCommon.Analysis.MatrixBlockOperators
import Mathlib.Analysis.MeanInequalities

/-! Hilbert--Schmidt comparisons for actual finite ℓ₂ operator spaces.
The auxiliary square-sum norm never replaces the operator-space norm. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def matrixHilbertExponent : BanachExponent := ⟨2, by norm_num⟩

@[simp] theorem matrixHilbertExponent_val : matrixHilbertExponent.val = 2 := rfl

theorem finiteLpTwo_norm_sq {N : ℕ} (x : FiniteLpSpace 𝕜 matrixHilbertExponent N) :
    ‖x‖ ^ 2 = ∑ i : Fin N, ‖x i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa [tsum_fintype] using h

theorem finiteMatrix_apply_eq_sum (p : BanachExponent) {N : ℕ}
    (A : FiniteMatrixBlock 𝕜 p N) (x : FiniteLpSpace 𝕜 p N) (i : Fin N) :
    A x i = ∑ j : Fin N, x j * matrixEntry p i j A := by
  classical
  have hx : x = ∑ j : Fin N, x j • lp.single p.val j (1 : 𝕜) := by
    apply lp.ext
    funext k
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      lp.single_apply, Pi.single_apply, smul_eq_mul]
    simp
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, matrixEntry_apply]

theorem matrixHilbertSchmidtNorm_sq (p : BanachExponent) {N : ℕ}
    (A : FiniteMatrixBlock 𝕜 p N) :
    matrixHilbertSchmidtNorm p A ^ 2 =
      ∑ i : Fin N, ∑ j : Fin N, ‖matrixEntry p i j A‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem matrixHilbertSchmidtNorm_le_sqrt_mul_norm {N : ℕ}
    (A : FiniteMatrixBlock 𝕜 matrixHilbertExponent N) :
    matrixHilbertSchmidtNorm matrixHilbertExponent A ≤ Real.sqrt (N : ℝ) * ‖A‖ := by
  have hcol (j : Fin N) :
      ∑ i : Fin N, ‖matrixEntry matrixHilbertExponent i j A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    change (∑ i : Fin N, ‖A (lp.single 2 j (1 : 𝕜)) i‖ ^ 2) ≤ ‖A‖ ^ 2
    rw [← finiteLpTwo_norm_sq (A (lp.single 2 j (1 : 𝕜)))]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg A)).mpr
    simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one] using
      A.le_opNorm (lp.single 2 j (1 : 𝕜))
  have hsum : (∑ i : Fin N, ∑ j : Fin N, ‖matrixEntry matrixHilbertExponent i j A‖ ^ 2) ≤
      (N : ℝ) * ‖A‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum (fun j _ => hcol j)).trans_eq (by simp)
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_⟩
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] using hsum

theorem matrixHilbertSchmidtNorm_le_rpow_mul_norm {N : ℕ}
    (A : FiniteMatrixBlock 𝕜 matrixHilbertExponent N) :
    matrixHilbertSchmidtNorm matrixHilbertExponent A ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ‖A‖ := by
  simpa only [Real.sqrt_eq_rpow] using matrixHilbertSchmidtNorm_le_sqrt_mul_norm A

theorem norm_le_matrixHilbertSchmidtNorm {N : ℕ}
    (A : FiniteMatrixBlock 𝕜 matrixHilbertExponent N) :
    ‖A‖ ≤ matrixHilbertSchmidtNorm matrixHilbertExponent A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hrow (i : Fin N) : ‖A x i‖ ^ 2 ≤
      (∑ j : Fin N, ‖matrixEntry matrixHilbertExponent i j A‖ ^ 2) * ‖x‖ ^ 2 := by
    have hn : ‖A x i‖ ≤ ∑ j : Fin N, ‖matrixEntry matrixHilbertExponent i j A‖ * ‖x j‖ := by
      rw [finiteMatrix_apply_eq_sum]
      exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun _ _ => by rw [norm_mul, mul_comm]))
    calc
      _ ≤ (∑ j : Fin N, ‖matrixEntry matrixHilbertExponent i j A‖ * ‖x j‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr hn
      _ ≤ (∑ j : Fin N, ‖matrixEntry matrixHilbertExponent i j A‖ ^ 2) *
          ∑ j : Fin N, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by rw [← finiteLpTwo_norm_sq x]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  calc
    ‖A x‖ ^ 2 = ∑ i : Fin N, ‖A x i‖ ^ 2 := finiteLpTwo_norm_sq _
    _ ≤ ∑ i : Fin N, (∑ j : Fin N, ‖matrixEntry matrixHilbertExponent i j A‖ ^ 2) * ‖x‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (matrixHilbertSchmidtNorm matrixHilbertExponent A * ‖x‖) ^ 2 := by
      rw [← Finset.sum_mul, mul_pow, matrixHilbertSchmidtNorm_sq]

end ThesisCommon
