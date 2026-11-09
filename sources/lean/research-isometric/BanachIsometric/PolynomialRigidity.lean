import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The algebraic last step of Theorem 3.1

This file does not establish polynomiality from an exact family of section maps.
It proves the subsequent extraction step: polynomiality of two consecutive even
powers forces polynomiality of the square. Positive homogeneity then forces the
resulting polynomial to be homogeneous of degree two, and positivity away from
zero is retained. The divisibility argument uses the integrally closed domain
theorem instead of explicit irreducible multiplicities.
-/

namespace BanachIsometric

/-- The divisibility step in the final paragraph of Theorem 3.1.
An integrally closed domain suffices; unique factorisation is stronger than needed. -/
theorem dvd_of_consecutive_power_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {a : ℕ} (ha : 0 < a) {P Q : R} (h : Q ^ a = P ^ (a + 1)) : P ∣ Q := by
  apply (IsIntegrallyClosed.pow_dvd_pow_iff (Nat.ne_of_gt ha)).mp
  rw [h]
  exact pow_dvd_pow P (Nat.le_succ a)

/-- A real function on coordinate space is represented by a multivariate polynomial. -/
def IsPolynomialFunction {σ : Type*} (f : (σ → ℝ) → ℝ) : Prop :=
  ∃ P : MvPolynomial σ ℝ, ∀ x, MvPolynomial.eval x P = f x

/-- Algebraic extraction of the square from two consecutive even polynomial powers.
No positivity, homogeneity, or regularity assumption is needed for this step. -/
theorem square_isPolynomialFunction_of_consecutive_even_powers
    {σ : Type*} {p : (σ → ℝ) → ℝ} {a : ℕ} (ha : 0 < a)
    (hP : IsPolynomialFunction (fun x => p x ^ (2 * a)))
    (hQ : IsPolynomialFunction (fun x => p x ^ (2 * a + 2))) :
    IsPolynomialFunction (fun x => p x ^ 2) := by
  obtain ⟨P, hP⟩ := hP
  obtain ⟨Q, hQ⟩ := hQ
  have hpow : Q ^ a = P ^ (a + 1) := by
    apply MvPolynomial.funext
    intro x
    simp only [map_pow, hP, hQ, ← pow_mul]
    congr 1
    ring
  by_cases hP0 : P = 0
  · refine ⟨0, ?_⟩
    intro x
    have hx : p x ^ (2 * a) = 0 := by simpa [hP0] using (hP x).symm
    have hx0 : p x = 0 := (pow_eq_zero hx)
    simp [hx0]
  obtain ⟨R, hR⟩ := dvd_of_consecutive_power_eq ha hpow
  have hRa : R ^ a = P := by
    have hPa : P ^ a ≠ 0 := pow_ne_zero _ hP0
    apply mul_left_cancel₀ hPa
    calc
      P ^ a * R ^ a = (P * R) ^ a := (mul_pow P R a).symm
      _ = Q ^ a := by rw [← hR]
      _ = P ^ (a + 1) := hpow
      _ = P ^ a * P := pow_succ P a
  refine ⟨R, ?_⟩
  intro x
  by_cases hpx : p x = 0
  · have hx : MvPolynomial.eval x R ^ a = 0 := by
      calc
        MvPolynomial.eval x R ^ a = MvPolynomial.eval x (R ^ a) := (map_pow _ _ _).symm
        _ = MvPolynomial.eval x P := by rw [hRa]
        _ = p x ^ (2 * a) := hP x
        _ = 0 := by simp [hpx, Nat.ne_of_gt ha]
    have hx0 : MvPolynomial.eval x R = 0 := pow_eq_zero hx
    simp [hx0, hpx]
  · have hPeval : MvPolynomial.eval x P ≠ 0 := by
      rw [hP x]
      exact pow_ne_zero _ hpx
    apply mul_left_cancel₀ hPeval
    calc
      MvPolynomial.eval x P * MvPolynomial.eval x R = MvPolynomial.eval x Q := by
        rw [hR, map_mul]
      _ = p x ^ (2 * a + 2) := hQ x
      _ = MvPolynomial.eval x P * p x ^ 2 := by rw [hP x, pow_add]

private noncomputable def scaleVariables {σ : Type*} (c : ℝ)
    (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ d ∈ P.support, MvPolynomial.monomial d (c ^ d.degree * P.coeff d)

private theorem coeff_scaleVariables {σ : Type*} (c : ℝ)
    (P : MvPolynomial σ ℝ) (d : σ →₀ ℕ) :
    (scaleVariables c P).coeff d = c ^ d.degree * P.coeff d := by
  classical
  by_cases hd : d ∈ P.support
  · simp [scaleVariables, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hd]
  · have hcoeff : P.coeff d = 0 := MvPolynomial.notMem_support_iff.mp hd
    simp [scaleVariables, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hd, hcoeff]

private theorem eval_scaleVariables {σ : Type*} (c : ℝ)
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    MvPolynomial.eval x (scaleVariables c P) =
      MvPolynomial.eval (fun i => c * x i) P := by
  classical
  unfold scaleVariables
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.eval_eq]
  simp only [MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree]
  ring

/-- A polynomial satisfying the degree-`n` scaling law at the single scalar `2`
is homogeneous of degree `n`. This is enough to reconstruct quadratic homogeneity
after extracting a polynomial square. -/
theorem isHomogeneous_of_eval_two_mul {σ : Type*} (P : MvPolynomial σ ℝ) (n : ℕ)
    (hscale : ∀ x : σ → ℝ,
      MvPolynomial.eval (fun i => (2 : ℝ) * x i) P =
        (2 : ℝ) ^ n * MvPolynomial.eval x P) : P.IsHomogeneous n := by
  classical
  have hpoly : scaleVariables 2 P = MvPolynomial.C ((2 : ℝ) ^ n) * P := by
    apply MvPolynomial.funext
    intro x
    rw [eval_scaleVariables, hscale, map_mul, MvPolynomial.eval_C]
  intro d hd
  have hcoeff := congrArg (MvPolynomial.coeff d) hpoly
  rw [coeff_scaleVariables, MvPolynomial.coeff_C_mul] at hcoeff
  have hpow : (2 : ℝ) ^ d.degree = (2 : ℝ) ^ n := mul_right_cancel₀ hd hcoeff
  change (Finsupp.weight (fun _ : σ => (1 : ℕ))) d = n
  rw [← Finsupp.degree_eq_weight_one]
  exact pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) hpow

/-- The complete polynomial extraction and degree-two homogeneity step in the
last paragraph of Theorem 3.1, with the earlier polynomiality conclusion explicit.
The scaling assumption is stated only at `2`, so positive homogeneity suffices. -/
theorem exists_homogeneous_square_of_consecutive_even_powers
    {σ : Type*} {p : (σ → ℝ) → ℝ} {a : ℕ} (ha : 0 < a)
    (hscale : ∀ x : σ → ℝ, p (fun i => (2 : ℝ) * x i) = 2 * p x)
    (hP : IsPolynomialFunction (fun x => p x ^ (2 * a)))
    (hQ : IsPolynomialFunction (fun x => p x ^ (2 * a + 2))) :
    ∃ R : MvPolynomial σ ℝ, R.IsHomogeneous 2 ∧
      ∀ x, MvPolynomial.eval x R = p x ^ 2 := by
  obtain ⟨R, hR⟩ := square_isPolynomialFunction_of_consecutive_even_powers ha hP hQ
  refine ⟨R, isHomogeneous_of_eval_two_mul R 2 ?_, hR⟩
  intro x
  simp only [hR]
  rw [hscale]
  ring

/-- Positivity away from the origin is retained by the homogeneous quadratic
polynomial extracted above. This is the positive-definiteness assertion in the
polynomial formulation of the last paragraph of Theorem 3.1. -/
theorem exists_positive_homogeneous_square_of_consecutive_even_powers
    {σ : Type*} {p : (σ → ℝ) → ℝ} {a : ℕ} (ha : 0 < a)
    (hscale : ∀ x : σ → ℝ, p (fun i => (2 : ℝ) * x i) = 2 * p x)
    (hpos : ∀ x : σ → ℝ, x ≠ 0 → 0 < p x)
    (hP : IsPolynomialFunction (fun x => p x ^ (2 * a)))
    (hQ : IsPolynomialFunction (fun x => p x ^ (2 * a + 2))) :
    ∃ R : MvPolynomial σ ℝ, R.IsHomogeneous 2 ∧
      (∀ x, MvPolynomial.eval x R = p x ^ 2) ∧
      ∀ x : σ → ℝ, x ≠ 0 → 0 < MvPolynomial.eval x R := by
  obtain ⟨R, hhom, hR⟩ :=
    exists_homogeneous_square_of_consecutive_even_powers ha hscale hP hQ
  refine ⟨R, hhom, hR, ?_⟩
  intro x hx
  rw [hR]
  exact pow_pos (hpos x hx) 2

end BanachIsometric
