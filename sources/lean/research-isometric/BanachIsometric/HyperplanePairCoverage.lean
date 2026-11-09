import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Every pair lies in a scalar hyperplane

This argument works over any division ring, including the opposite quaternion
algebra used for right quaternionic spaces. It supplies the pair-coverage
condition in the real section theorem from scalar dimension at least three.
-/

namespace BanachIsometric

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The span of two vectors is proper in scalar dimension at least three,
so a nonzero scalar functional vanishes on both. -/
theorem exists_nonzero_functional_annihilating_pair
    (hdim : 3 ≤ Module.finrank K V) (x y : V) :
    ∃ f : V →ₗ[K] K, f ≠ 0 ∧ f x = 0 ∧ f y = 0 := by
  classical
  let p : Submodule K V := Submodule.span K ({x, y} : Set V)
  have hpdim : Module.finrank K p ≤ 2 := by
    have h := finrank_span_finset_le_card (R := K) ({x, y} : Finset V)
    have hc : ({x, y} : Finset V).card ≤ 2 := by
      by_cases hxy : x = y <;> simp [hxy]
    exact (show Module.finrank K p ≤ ({x, y} : Finset V).card by
      simpa only [p, Finset.coe_insert, Finset.coe_singleton] using h).trans hc
  have hp : p < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by omega)
  obtain ⟨f, hf, hpf⟩ := p.exists_le_ker_of_lt_top hp
  refine ⟨f, hf, ?_, ?_⟩
  · exact hpf (Submodule.subset_span (by simp))
  · exact hpf (Submodule.subset_span (by simp))

/-- A nonzero functional over a division ring is surjective; the order of
multiplication here also covers noncommutative scalars. -/
theorem nonzero_functional_surjective {f : V →ₗ[K] K} (hf : f ≠ 0) :
    Function.Surjective f := by
  obtain ⟨z, hz⟩ : ∃ z : V, f z ≠ 0 := by
    by_contra h
    apply hf
    ext z
    simpa using not_exists.mp h z
  intro a
  refine ⟨(a * (f z)⁻¹) • z, ?_⟩
  rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hz, mul_one]

/-- Every pair belongs to a scalar hyperplane, with codimension proved by
the dimension of its actual quotient. -/
theorem exists_hyperplane_containing_pair
    (hdim : 3 ≤ Module.finrank K V) (x y : V) :
    ∃ H : Submodule K V, x ∈ H ∧ y ∈ H ∧ Module.finrank K (V ⧸ H) = 1 := by
  obtain ⟨f, hf, hfx, hfy⟩ := exists_nonzero_functional_annihilating_pair hdim x y
  refine ⟨LinearMap.ker f, hfx, hfy, ?_⟩
  rw [f.quotKerEquivRange.finrank_eq]
  rw [LinearMap.range_eq_top.mpr (nonzero_functional_surjective hf),
    finrank_top, Module.finrank_self]

end DivisionRing

section InnerProduct

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]

/-- Over the real or complex field, the covering hyperplane can be specified
by an actual unit normal vector for the given inner product. -/
theorem exists_unit_normal_annihilating_pair
    (hdim : 3 ≤ Module.finrank 𝕜 V) (x y : V) :
    ∃ u : V, ‖u‖ = 1 ∧ inner 𝕜 u x = 0 ∧ inner 𝕜 u y = 0 := by
  letI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  obtain ⟨f, hf, hfx, hfy⟩ := exists_nonzero_functional_annihilating_pair hdim x y
  let ℓ : V →L[𝕜] 𝕜 := LinearMap.toContinuousLinearMap f
  let u : V := (InnerProductSpace.toDual 𝕜 V).symm ℓ
  have hinner (z : V) : inner 𝕜 u z = f z := by
    exact InnerProductSpace.toDual_symm_apply
  have hu : u ≠ 0 := by
    intro hz
    apply hf
    ext z
    simpa only [hz, inner_zero_left] using (hinner z).symm
  refine ⟨(‖u‖ : 𝕜)⁻¹ • u, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)
  · rw [inner_smul_left, hinner, hfx, mul_zero]
  · rw [inner_smul_left, hinner, hfy, mul_zero]

end InnerProduct

end BanachIsometric
