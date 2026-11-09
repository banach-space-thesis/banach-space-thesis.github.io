import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Actual coefficient functionals for a nonzero nilpotent element

The minimal polynomial and its prime-power factorization derive a finite
linearly independent initial power family. Its actual linear-combination map
has a proved left inverse, giving coefficient functionals on the whole algebra.
These are algebraic prerequisites for the primitive-element obstruction in
rational Hopf arguments, not an assumed topological comparison theorem.
-/

noncomputable section
namespace BanachIsometric

open Polynomial

theorem exists_nilpotent_power_coordinates
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [Nontrivial A]
    {x : A} (hx : IsNilpotent x) (hne : x ≠ 0) :
    ∃ n : ℕ, 2 ≤ n ∧ x ^ n = 0 ∧
      LinearIndependent K (fun i : Fin n => x ^ (i : ℕ)) := by
  obtain ⟨m, hm⟩ := hx
  have hint : IsIntegral K x := ⟨X ^ m, monic_X_pow m, by simpa using hm⟩
  have hdiv : minpoly K x ∣ (X : K[X]) ^ m := minpoly.dvd K x (by simpa only [aeval_X_pow] using hm)
  obtain ⟨n, _hnm, hassoc⟩ := (dvd_prime_pow (prime_X : Prime (X : K[X])) m).mp hdiv
  have hmin : minpoly K x = (X : K[X]) ^ n :=
    eq_of_monic_of_associated (minpoly.monic hint) (monic_X_pow n) hassoc
  have hxn : x ^ n = 0 := by
    have h := minpoly.aeval K x
    rwa [hmin, aeval_X_pow] at h
  have hn : 2 ≤ n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    interval_cases n <;> simp_all
  refine ⟨n, hn, hxn, ?_⟩
  have h := linearIndependent_pow (K := K) x
  rw [hmin, natDegree_X_pow] at h
  exact h

theorem exists_linear_power_coefficient
    {K A : Type*} [Field K] [Ring A] [Algebra K A] {n : ℕ} {x : A}
    (hlin : LinearIndependent K (fun i : Fin n => x ^ (i : ℕ))) (j : Fin n) :
    ∃ f : A →ₗ[K] K, ∀ i : Fin n, f (x ^ (i : ℕ)) = if i = j then 1 else 0 := by
  classical
  let T := Finsupp.linearCombination K (fun i : Fin n => x ^ (i : ℕ))
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective (linearIndependent_iff_ker.mp hlin)
  let f : A →ₗ[K] K := (Finsupp.lapply j).comp L
  refine ⟨f, ?_⟩
  intro i
  have hi := congrArg (fun g : (Fin n →₀ K) →ₗ[K] (Fin n →₀ K) => g (Finsupp.single i 1)) hL
  change L (T (Finsupp.single i 1)) = Finsupp.single i 1 at hi
  simp only [T, Finsupp.linearCombination_single, one_smul] at hi
  change (L (x ^ (i : ℕ))) j = _
  rw [hi]
  simp only [Finsupp.single_apply]

end BanachIsometric
