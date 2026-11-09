import BanachIsometric.HermitianRelativeOperator

/-!
# Rayleigh and trace invariants of the actual relative Hermitian operator

These are proved from the represented form and actual orthonormal bases.
They will replace characteristic-polynomial multiset bookkeeping in the
one-eigenvector-deletion argument.
-/

namespace BanachIsometric

open scoped BigOperators ComplexConjugate

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  {ι : Type*} [Fintype ι]

omit [FiniteDimensional 𝕜 E] in
theorem re_inner_apply_eq_sum_eigenvalues (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι 𝕜 E) (a : ι → ℝ)
    (heig : ∀ i, T (b i) = (a i : 𝕜) • b i) (x : E) :
    RCLike.re (inner 𝕜 x (T x)) = ∑ i, a i * ‖inner 𝕜 (b i) x‖ ^ 2 := by
  rw [← b.sum_inner_mul_inner x (T x), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hrep : inner 𝕜 (b i) (T x) = (a i : 𝕜) * inner 𝕜 (b i) x := by
    rw [← hT, heig, inner_smul_left]
    simp only [RCLike.conj_ofReal]
  rw [hrep, show inner 𝕜 x (b i) * ((a i : 𝕜) * inner 𝕜 (b i) x) =
    (a i : 𝕜) * (inner 𝕜 x (b i) * inner 𝕜 (b i) x) by ring,
    RCLike.re_ofReal_mul, inner_mul_symm_re_eq_norm, norm_mul, norm_inner_symm x (b i)]
  ring

omit [FiniteDimensional 𝕜 E] in
theorem re_inner_apply_le_eigenvalue_bound (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι 𝕜 E) (a : ι → ℝ)
    (heig : ∀ i, T (b i) = (a i : 𝕜) • b i) {M : ℝ} (hM : ∀ i, a i ≤ M) (x : E) :
    RCLike.re (inner 𝕜 x (T x)) ≤ M * ‖x‖ ^ 2 := by
  rw [re_inner_apply_eq_sum_eigenvalues T hT b a heig, ← b.sum_sq_norm_inner_right x,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hM i) (sq_nonneg _)

omit [FiniteDimensional 𝕜 E] in
theorem trace_eq_sum_inner_orthonormalBasis (T : E →ₗ[𝕜] E)
    (b : OrthonormalBasis ι 𝕜 E) :
    LinearMap.trace 𝕜 E T = ∑ i, inner 𝕜 (b i) (T (b i)) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis]
  change (∑ i, b.toBasis.repr (T (b i)) i) = _
  simp only [b.coe_toBasis_repr_apply, b.repr_apply_apply]

theorem re_trace_relativeOperator_eq_sum (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜)
    (hB : ∀ x y, star (B x y) = B y x) (b : OrthonormalBasis ι 𝕜 E) :
    RCLike.re (LinearMap.trace 𝕜 E (hermitianRelativeOperator B)) =
      ∑ i, RCLike.re (B (b i) (b i)) := by
  rw [trace_eq_sum_inner_orthonormalBasis _ b, map_sum]
  simp only [inner_hermitianRelativeOperator B hB]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Actual isometric change of section coordinates and diagonal scaling
imply trace scaling. No conjugacy or eigenvalue matching is assumed. -/
theorem re_trace_relativeOperator_scaling_of_isometry
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (C : F →ₗ⋆[𝕜] F →ₗ[𝕜] 𝕜)
    (hB : ∀ x y, star (B x y) = B y x) (hC : ∀ x y, star (C x y) = C y x)
    (U : E ≃ₗᵢ[𝕜] F) (c : ℝ)
    (hscale : ∀ x, RCLike.re (C (U x) (U x)) = c * RCLike.re (B x x)) :
    RCLike.re (LinearMap.trace 𝕜 F (hermitianRelativeOperator C)) =
      c * RCLike.re (LinearMap.trace 𝕜 E (hermitianRelativeOperator B)) := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [re_trace_relativeOperator_eq_sum C hC (b.map U),
    re_trace_relativeOperator_eq_sum B hB b, Finset.mul_sum]
  simp only [OrthonormalBasis.map_apply, hscale]

end

end BanachIsometric
