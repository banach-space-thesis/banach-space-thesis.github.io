import BanachIsometric.NilpotentPowerCoordinates
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.GradedMonoid

/-!
# The binomial coproduct obstruction, without an ordinary-bialgebra assumption

The multiplication on `A` need not commute. A linear coproduct with the stated
actual power identities has no nonzero nilpotent candidate in characteristic
zero. The one-element multiplicative step derives those identities internally.
Bounded positive grading supplies nilpotence. A genuine graded-bialgebra
application still has to prove this step with its actual Koszul signs; no
graded or topological comparison is postulated here.
-/

noncomputable section
namespace BanachIsometric

open scoped TensorProduct BigOperators

theorem eq_zero_of_nilpotent_binomial_coproduct
    {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A] [Nontrivial A]
    (Δ : A →ₗ[K] A ⊗[K] A) {x : A}
    (hpower : ∀ n : ℕ, Δ (x ^ n) =
      ∑ i ∈ Finset.range (n + 1), n.choose i • ((x ^ i) ⊗ₜ[K] (x ^ (n - i))))
    (hx : IsNilpotent x) : x = 0 := by
  classical
  by_contra hne
  obtain ⟨n, hn, hxn, hlin⟩ := exists_nilpotent_power_coordinates (K := K) hx hne
  let j : Fin n := ⟨n - 1, by omega⟩
  obtain ⟨f, hf⟩ := exists_linear_power_coefficient hlin j
  let F : A ⊗[K] A →ₗ[K] A := TensorProduct.lift (LinearMap.lsmul K A ∘ₗ f)
  have hF (a b : A) : F (a ⊗ₜ[K] b) = f a • b := by
    simp only [F, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply]
  have hsum :
      (∑ i ∈ Finset.range (n + 1), n.choose i • (f (x ^ i) • x ^ (n - i))) = n • x := by
    rw [Finset.sum_eq_single (n - 1)]
    · have hj : f (x ^ (n - 1)) = 1 := by simpa only [j, ite_true] using hf j
      have hsub : n - (n - 1) = 1 := by omega
      rw [hj, one_smul, hsub, pow_one, Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
    · intro i hi hneq
      have hfi : f (x ^ i) = 0 := by
        by_cases hil : i < n
        · have hij : (⟨i, hil⟩ : Fin n) ≠ j := fun he => hneq (congrArg Fin.val he)
          simpa only [Fin.val_mk, if_neg hij] using hf ⟨i, hil⟩
        · have hieq : i = n := by have := Finset.mem_range.mp hi; omega
          rw [hieq, hxn, map_zero]
      rw [hfi, zero_smul, smul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  have h := congrArg F (hpower n)
  rw [hxn, map_zero, map_zero] at h
  simp only [map_sum, map_nsmul, hF] at h
  rw [hsum] at h
  have hncast : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  have hsmul : (n : K) • x = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h.symm
  exact hne ((smul_eq_zero.mp hsmul).resolve_left hncast)

theorem binomial_coproduct_powers_of_step
    {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A]
    (Δ : A →ₗ[K] A ⊗[K] A) (hunit : Δ 1 = 1) {x : A}
    (hstep : ∀ y : A, Δ (x * y) = (x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x) * Δ y) (n : ℕ) :
    Δ (x ^ n) =
      ∑ i ∈ Finset.range (n + 1), n.choose i • ((x ^ i) ⊗ₜ[K] (x ^ (n - i))) := by
  have hpow (m : ℕ) : Δ (x ^ m) = (x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x) ^ m := by
    induction m with
    | zero => simpa only [pow_zero] using hunit
    | succ m ih => rw [pow_succ', hstep, ih, pow_succ']
  have hcomm : Commute (x ⊗ₜ[K] (1 : A)) (1 ⊗ₜ[K] x) := by
    show (x ⊗ₜ[K] (1 : A)) * (1 ⊗ₜ[K] x) = (1 ⊗ₜ[K] x) * (x ⊗ₜ[K] (1 : A))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hpow, hcomm.add_pow', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem isNilpotent_of_bounded_positive_grading
    {K A : Type*} [Semiring K] [Ring A] [Module K A]
    (𝒜 : ℕ → Submodule K A) [SetLike.GradedMonoid 𝒜]
    (N : ℕ) (hbound : ∀ d : ℕ, N < d → 𝒜 d = ⊥)
    {d : ℕ} (hd : 0 < d) {x : A} (hx : x ∈ 𝒜 d) : IsNilpotent x := by
  refine ⟨N + 1, ?_⟩
  have hdegree : N < (N + 1) * d := lt_of_lt_of_le (Nat.lt_succ_self N)
    (by simpa only [mul_one] using Nat.mul_le_mul_left (N + 1) (show 1 ≤ d by omega))
  have hp : x ^ (N + 1) ∈ 𝒜 ((N + 1) * d) := by
    simpa only [nsmul_eq_mul] using SetLike.pow_mem_graded (N + 1) hx
  simpa only [hbound _ hdegree, Submodule.mem_bot] using hp

theorem eq_zero_of_bounded_grading_coproduct_step
    {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A] [Nontrivial A]
    (𝒜 : ℕ → Submodule K A) [SetLike.GradedMonoid 𝒜]
    (N : ℕ) (hbound : ∀ d : ℕ, N < d → 𝒜 d = ⊥)
    (Δ : A →ₗ[K] A ⊗[K] A) (hunit : Δ 1 = 1)
    {d : ℕ} (hd : 0 < d) {x : A} (hx : x ∈ 𝒜 d)
    (hstep : ∀ y : A, Δ (x * y) = (x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x) * Δ y) : x = 0 :=
  eq_zero_of_nilpotent_binomial_coproduct Δ (binomial_coproduct_powers_of_step Δ hunit hstep)
    (isNilpotent_of_bounded_positive_grading 𝒜 N hbound hd hx)

end BanachIsometric
