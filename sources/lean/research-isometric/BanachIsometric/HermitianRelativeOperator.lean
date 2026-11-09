import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Trace

/-!
# The actual operator of a second Hermitian square

The ambient inner product and its norm are fixed. Riesz representation of the
second form constructs its relative operator; linearity, self-adjointness and
positive eigenvalues are proved from the form. The orthonormal eigenbasis is
supplied by the spectral theorem, not assumed as geometric data.
-/

namespace BanachIsometric

open scoped ComplexConjugate

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- Relative Riesz operator for an algebraic sesquilinear form in finite
dimensions. Only the linear functional in the second slot is completed. -/
def hermitianRelativeOperator (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) : E →ₗ[𝕜] E where
  toFun x := (InnerProductSpace.toDual 𝕜 E).symm (LinearMap.toContinuousLinearMap (B x))
  map_add' x y := by
    have hB : LinearMap.toContinuousLinearMap (B (x + y)) =
        LinearMap.toContinuousLinearMap (B x) + LinearMap.toContinuousLinearMap (B y) := by
      ext z
      exact congrArg (fun f : E →ₗ[𝕜] 𝕜 => f z) (B.map_add x y)
    rw [hB, map_add]
  map_smul' a x := by
    have hB : LinearMap.toContinuousLinearMap (B (a • x)) =
        star a • LinearMap.toContinuousLinearMap (B x) := by
      ext z
      exact congrArg (fun f : E →ₗ[𝕜] 𝕜 => f z) (B.map_smulₛₗ a x)
    rw [hB, map_smulₛₗ]
    simp only [starRingEnd_apply, star_star, RingHom.id_apply]

theorem hermitianRelativeOperator_inner (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (x y : E) :
    inner 𝕜 (hermitianRelativeOperator B x) y = B x y :=
  InnerProductSpace.toDual_symm_apply

theorem inner_hermitianRelativeOperator (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜)
    (hB : ∀ x y, star (B x y) = B y x) (x y : E) :
    inner 𝕜 x (hermitianRelativeOperator B y) = B x y := by
  rw [← inner_conj_symm, hermitianRelativeOperator_inner]
  exact hB y x

theorem hermitianRelativeOperator_isSymmetric (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜)
    (hB : ∀ x y, star (B x y) = B y x) :
    (hermitianRelativeOperator B).IsSymmetric := by
  intro x y
  rw [hermitianRelativeOperator_inner, inner_hermitianRelativeOperator B hB]

/-- An actual positive Hermitian form has an actual positive spectral
decomposition for its Riesz operator, over either `ℝ` or `ℂ`. -/
theorem exists_positive_eigenbasis_hermitianRelativeOperator
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hB : ∀ x y, star (B x y) = B y x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < RCLike.re (B x x))
    {n : ℕ} (hdim : Module.finrank 𝕜 E = n) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 E, ∃ a : Fin n → ℝ,
      (∀ i, 0 < a i) ∧
      ∀ i, hermitianRelativeOperator B (b i) = (a i : 𝕜) • b i := by
  let hR := hermitianRelativeOperator_isSymmetric B hB
  let b := hR.eigenvectorBasis hdim
  let a := hR.eigenvalues hdim
  refine ⟨b, a, ?_, hR.apply_eigenvectorBasis hdim⟩
  intro i
  have hn : ‖b i‖ = 1 := b.orthonormal.1 i
  have hne : b i ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have heig : hermitianRelativeOperator B (b i) = (a i : 𝕜) • b i :=
    hR.apply_eigenvectorBasis hdim i
  have hval : RCLike.re (B (b i) (b i)) = a i := by
    rw [← inner_hermitianRelativeOperator B hB, heig, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hn]
    simp only [RCLike.ofReal_one, one_pow, mul_one, RCLike.ofReal_re]
  rw [← hval]
  exact hpos (b i) hne

end

end BanachIsometric
