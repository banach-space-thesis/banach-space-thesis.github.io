import BanachIsometric.HermitianSimilarityRigidity
import BanachIsometric.FiniteConfigurations

/-!
# Global proportionality from the actual simultaneous section similarities

The two functions share each scalar-linear similarity, with possibly different
positive constants. Their restrictions inherit that exact hypothesis. Local
spectral rigidity is applied on a genuine finite-dimensional subspace through
a fixed nonzero anchor and the arbitrary test vector. No local proportionality
or eigenvalue conclusion is assumed in the final theorem.
-/

namespace BanachIsometric

noncomputable section

section AlgebraicSimilarities

variable {𝕜 X : Type*} [DivisionRing 𝕜] [AddCommGroup X] [Module 𝕜 X]

/-- The two-member part of the original simultaneous similarity hypothesis:
the same scalar-linear map is a positive similarity for both functions. -/
def SimultaneousPairSimilarities (n : ℕ) (p q : X → ℝ) : Prop :=
  ∀ H J : Submodule 𝕜 X, Module.finrank 𝕜 H = n → Module.finrank 𝕜 J = n →
    ∃ T : H ≃ₗ[𝕜] J, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (∀ x, p (T x : X) = c₁ * p (x : X)) ∧
      ∀ x, q (T x : X) = c₂ * q (x : X)

theorem SimultaneousPairSimilarities.restrict {n : ℕ} {p q : X → ℝ}
    (h : SimultaneousPairSimilarities (𝕜 := 𝕜) n p q) (Y : Submodule 𝕜 X) :
    SimultaneousPairSimilarities (𝕜 := 𝕜) n (fun y : Y => p y.val) (fun y : Y => q y.val) := by
  intro H J hH hJ
  let eH := Submodule.equivMapOfInjective Y.subtype Subtype.val_injective H
  let eJ := Submodule.equivMapOfInjective Y.subtype Subtype.val_injective J
  obtain ⟨T, c₁, c₂, hc₁, hc₂, hp, hq⟩ := h (H.map Y.subtype) (J.map Y.subtype)
    (eH.finrank_eq.symm.trans hH) (eJ.finrank_eq.symm.trans hJ)
  let U := eH.trans (T.trans eJ.symm)
  have hval (x : H) : ((U x : Y) : X) = (T (eH x) : X) :=
    congrArg Subtype.val (eJ.apply_symm_apply (T (eH x)))
  refine ⟨U, c₁, c₂, hc₁, hc₂, ?_, ?_⟩
  · intro x
    change p ((U x : Y) : X) = c₁ * p (x.val : X)
    rw [hval]
    exact hp (eH x)
  · intro x
    change q ((U x : Y) : X) = c₂ * q (x.val : X)
    rw [hval]
    exact hq (eH x)

end AlgebraicSimilarities

section FiniteNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

theorem hermitianNorm_proportional_of_simultaneous_similarities
    {n : ℕ} (hn : 2 ≤ n) (hdim : Module.finrank 𝕜 E = n + 1)
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hB : ∀ x y, star (B x y) = B y x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < RCLike.re (B x x))
    (q : E → ℝ) (hqnonneg : ∀ x, 0 ≤ q x) (hqsq : ∀ x, RCLike.re (B x x) = q x ^ 2)
    (hsim : SimultaneousPairSimilarities (𝕜 := 𝕜) n norm q) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * ‖x‖ := by
  obtain ⟨A, hA, hquad⟩ := hermitianSquare_proportional_of_simultaneous_similarities hn hdim
    B hB hpos (fun H J hH hJ => by
      obtain ⟨T, c₁, c₂, hc₁, hc₂, hp, hq⟩ := hsim H J hH hJ
      refine ⟨T, c₁, c₂, hc₁, hc₂, hp, ?_⟩
      intro x
      rw [hqsq, hqsq, hq, mul_pow])
  refine ⟨Real.sqrt A, Real.sqrt_pos.mpr hA, ?_⟩
  intro x
  have hs : q x ^ 2 = (Real.sqrt A * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA.le, ← hqsq, hquad]
  exact (sq_eq_sq₀ (hqnonneg x) (mul_nonneg (Real.sqrt_nonneg A) (norm_nonneg x))).mp hs

end FiniteNorm

section GlobalNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The spectral/global proportionality step of Theorem D over `ℝ` and `ℂ`.
The existing inner product induces the first given norm; the second is the
given nonnegative square root of its actual positive Hermitian form. -/
theorem hermitianNorm_global_proportional_of_simultaneous_similarities
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank 𝕜 E)
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hB : ∀ x y, star (B x y) = B y x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < RCLike.re (B x x))
    (q : E → ℝ) (hqnonneg : ∀ x, 0 ≤ q x) (hqsq : ∀ x, RCLike.re (B x x) = q x ^ 2)
    (hsim : SimultaneousPairSimilarities (𝕜 := 𝕜) n norm q) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * ‖x‖ := by
  have hrank : 0 < Module.rank 𝕜 E := (zero_le (n : Cardinal)).trans_lt hdim
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp hrank
  have hq₀ : 0 < q x₀ := by
    have hh := hpos x₀ hx₀
    rw [hqsq] at hh
    nlinarith [hqnonneg x₀]
  have hp₀ : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  refine ⟨q x₀ / ‖x₀‖, div_pos hq₀ hp₀, ?_⟩
  intro x
  obtain ⟨Y, hx₀Y, hxY, _, hfinite, hYdim⟩ := exists_subspace_containing_triple (K := 𝕜)
    (n + 1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hdim) x₀ x 0
  letI := hfinite
  let C := restrictSesqForm B Y
  have hC : ∀ y z, star (C y z) = C z y := restrictSesqForm_hermitian B hB Y
  have hCpos (y : Y) (hy : y ≠ 0) : 0 < RCLike.re (C y y) :=
    hpos y.val (fun h => hy (Subtype.ext h))
  obtain ⟨aY, _, hprop⟩ := hermitianNorm_proportional_of_simultaneous_similarities hn hYdim
    C hC hCpos (fun y : Y => q y.val) (fun y => hqnonneg y.val) (fun y => hqsq y.val)
    (hsim.restrict Y)
  have haY : aY = q x₀ / ‖x₀‖ := by
    apply (eq_div_iff hp₀.ne').mpr
    exact (hprop ⟨x₀, hx₀Y⟩).symm
  simpa only [haY] using hprop ⟨x, hxY⟩

end GlobalNorm

end

end BanachIsometric
