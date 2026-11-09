import BanachIsometric.QuaternionicSimilarityRigidity
import BanachIsometric.QuaternionicCompletion
import BanachIsometric.HermitianGlobalProportionality

/-!
# Global proportionality for the original right quaternionic Hermitian norms

Actual local trace rigidity is applied to a genuine finite right quaternionic
subspace through a fixed nonzero anchor and each test vector. Only canonical
real restrictions are used for real inner-product calculations; the original
right scalar action and original norm remain fixed.
-/

namespace BanachIsometric.Quaternionic

open scoped Quaternion

noncomputable section

section Finite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module Hᵐᵒᵖ E] [IsScalarTower ℝ Hᵐᵒᵖ E] [FiniteDimensional Hᵐᵒᵖ E]

theorem hermitianNorm_proportional_of_quaternionic_similarities
    {n : ℕ} (hn : 2 ≤ n) (hdim : Module.finrank Hᵐᵒᵖ E = n + 1)
    (P Q : HermitianForm E) (hP : ∀ x y, (P.form x y).re = inner ℝ x y)
    (hQpos : ∀ x : E, x ≠ 0 → 0 < (Q.form x x).re)
    (q : E → ℝ) (hqnonneg : ∀ x, 0 ≤ q x) (hqsq : ∀ x, (Q.form x x).re = q x ^ 2)
    (hsim : SimultaneousPairSimilarities (𝕜 := Hᵐᵒᵖ) n norm q) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * ‖x‖ := by
  obtain ⟨A, hA, hquad⟩ := hermitianSquare_proportional_of_quaternionic_similarities hn hdim
    P Q hP hQpos (fun S T hS hT => by
      obtain ⟨U, c₁, c₂, hc₁, hc₂, hp, hq⟩ := hsim S T hS hT
      refine ⟨U, c₁, c₂, hc₁, hc₂, hp, ?_⟩
      intro x
      rw [hqsq, hqsq, hq, mul_pow])
  refine ⟨Real.sqrt A, Real.sqrt_pos.mpr hA, ?_⟩
  intro x
  have hs : q x ^ 2 = (Real.sqrt A * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA.le, ← hqsq, hquad]
  exact (sq_eq_sq₀ (hqnonneg x) (mul_nonneg (Real.sqrt_nonneg A) (norm_nonneg x))).mp hs

end Finite

section Global

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module Hᵐᵒᵖ E] [IsScalarTower ℝ Hᵐᵒᵖ E]

theorem hermitianNorm_global_proportional_of_quaternionic_similarities
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ E)
    (P Q : HermitianForm E) (hP : ∀ x y, (P.form x y).re = inner ℝ x y)
    (hQpos : ∀ x : E, x ≠ 0 → 0 < (Q.form x x).re)
    (q : E → ℝ) (hqnonneg : ∀ x, 0 ≤ q x) (hqsq : ∀ x, (Q.form x x).re = q x ^ 2)
    (hsim : SimultaneousPairSimilarities (𝕜 := Hᵐᵒᵖ) n norm q) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * ‖x‖ := by
  have hrank : 0 < Module.rank Hᵐᵒᵖ E := (zero_le (n : Cardinal)).trans_lt hdim
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp hrank
  have hq₀ : 0 < q x₀ := by
    have hh := hQpos x₀ hx₀
    rw [hqsq] at hh
    nlinarith [hqnonneg x₀]
  have hp₀ : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  refine ⟨q x₀ / ‖x₀‖, div_pos hq₀ hp₀, ?_⟩
  intro x
  obtain ⟨Y, hx₀Y, hxY, _, hfinite, hYdim⟩ := exists_subspace_containing_triple (K := Hᵐᵒᵖ)
    (n + 1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hdim) x₀ x 0
  letI := hfinite
  let Yr := Y.restrictScalars ℝ
  let j : Yr →ₗ[Hᵐᵒᵖ] E := Y.subtype.comp (Y.restrictScalarsEquiv ℝ).toLinearMap
  letI : FiniteDimensional Hᵐᵒᵖ Yr :=
    Module.Finite.of_surjective (Y.restrictScalarsEquiv ℝ).symm.toLinearMap
      (Y.restrictScalarsEquiv ℝ).symm.surjective
  have hj : Function.Injective j := Subtype.val_injective.comp (Y.restrictScalarsEquiv ℝ).injective
  have hP' (y z : Yr) : ((P.comap j).form y z).re = inner ℝ y z := hP y.val z.val
  have hQ' (y : Yr) (hy : y ≠ 0) : 0 < ((Q.comap j).form y y).re :=
    hQpos (j y) (fun hz => hy (hj (hz.trans j.map_zero.symm)))
  have hdYr : Module.finrank Hᵐᵒᵖ Yr = n + 1 :=
    (Y.restrictScalarsEquiv ℝ).finrank_eq.trans hYdim
  obtain ⟨aY, _, hprop⟩ := hermitianNorm_proportional_of_quaternionic_similarities hn hdYr
    (P.comap j) (Q.comap j) hP' hQ' (fun y : Yr => q y.val)
    (fun y => hqnonneg y.val) (fun y => hqsq y.val) (hsim.restrict Y)
  have haY : aY = q x₀ / ‖x₀‖ := by
    apply (eq_div_iff hp₀.ne').mpr
    exact (hprop ⟨x₀, hx₀Y⟩).symm
  simpa only [haY] using hprop ⟨x, hxY⟩

end Global

section OriginalNorm

attribute [local instance] RestrictScalars.moduleOrig

variable {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]

/-- The original norm/form witnesses and original right-linear simultaneous
similarities imply global proportionality. The real inner product is installed
only on the canonical real restriction and retains the given norm exactly. -/
theorem quaternionic_norm_proportional_of_hermitian_similarities
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ V)
    (hp : HasHermitianSquare (norm : V → ℝ)) {q : V → ℝ}
    (hq : HasHermitianSquare q) (hqnonneg : ∀ x, 0 ≤ q x)
    (hsim : SimultaneousPairSimilarities (𝕜 := Hᵐᵒᵖ) n norm q) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * ‖x‖ := by
  obtain ⟨pForm, hpForm, _⟩ := hp
  obtain ⟨qForm, hqForm, hqPos⟩ := hq
  letI : InnerProductSpace ℝ (RestrictScalars ℝ Hᵐᵒᵖ V) :=
    realInnerProductSpaceOfHermitian pForm hpForm
  apply hermitianNorm_global_proportional_of_quaternionic_similarities
    (E := RestrictScalars ℝ Hᵐᵒᵖ V) hn hdim pForm qForm (fun _ _ => rfl) hqPos q hqnonneg _ hsim
  intro x
  exact congrArg QuaternionAlgebra.re (hqForm x)

end OriginalNorm

end

end BanachIsometric.Quaternionic
