import BanachIsometric.HermitianSpectralInvariants

/-!
# Saturation of a real self-adjoint Rayleigh bound by its actual trace

The actual spectral theorem is used internally. If every Rayleigh quotient is
at most `M` and the trace is dimension times `M`, every eigenvalue equals `M`.
This avoids a separate quaternionic spectral theorem in the application.
-/

namespace BanachIsometric

open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem trace_relativeOperator_of_scalar_diagonal
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (M : ℝ)
    (hdiag : ∀ x, B x x = M * ‖x‖ ^ 2) :
    LinearMap.trace ℝ E (hermitianRelativeOperator B) = (Module.finrank ℝ E : ℝ) * M := by
  let b := stdOrthonormalBasis ℝ E
  rw [trace_eq_sum_inner_orthonormalBasis _ b]
  simp_rw [inner_hermitianRelativeOperator B (fun x y => hB x y), hdiag, b.orthonormal.1,
    one_pow, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem symmetric_scalar_diagonal_of_trace_saturates_bound
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (M : ℝ)
    (hbound : ∀ x, inner ℝ x (T x) ≤ M * ‖x‖ ^ 2)
    (htrace : LinearMap.trace ℝ E T = (Module.finrank ℝ E : ℝ) * M) :
    ∀ x, inner ℝ x (T x) = M * ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let a := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have heig (i) : T (b i) = a i • b i := hT.apply_eigenvectorBasis rfl i
  have hle (i) : a i ≤ M := by
    have h := hbound (b i)
    simpa only [heig, inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1,
      one_pow, mul_one] using h
  have hsum : ∑ i, a i = (Module.finrank ℝ E : ℝ) * M := by
    rw [trace_eq_sum_inner_orthonormalBasis _ b] at htrace
    simpa only [heig, inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1,
      one_pow, mul_one] using htrace
  have hzero : ∑ i, (M - a i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self]
  have hall (i) : a i = M := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hle j))).mp hzero
      i (Finset.mem_univ i)
    linarith
  intro x
  have h := re_inner_apply_eq_sum_eigenvalues T hT b a heig x
  change inner ℝ x (T x) = _ at h
  rw [h]
  simp_rw [hall]
  rw [← Finset.mul_sum, b.sum_sq_norm_inner_right]

end

end BanachIsometric
