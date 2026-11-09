import BanachIsometric.PolynomialRigidity
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# From the extracted polynomial to an actual quadratic form

The homogeneous degree-two polynomial in Theorem 3.1 is converted into
Mathlib's `QuadraticForm`, with exactly the same values. This closes the
algebraic extraction step, while leaving the earlier polynomiality input
explicit.
-/

namespace BanachIsometric

private theorem degree_two_eq_sum_single {σ : Type*} (d : σ →₀ ℕ)
    (hd : d.degree = 2) :
    ∃ i j : σ, d = Finsupp.single i 1 + Finsupp.single j 1 := by
  classical
  have hcard : d.toMultiset.card = 2 := by
    simpa only [Finsupp.card_toMultiset, Finsupp.sum, Finsupp.degree] using hd
  obtain ⟨i, j, hij⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨i, j, (Finsupp.orderIsoMultiset : (σ →₀ ℕ) ≃o Multiset σ).injective ?_⟩
  change d.toMultiset = (Finsupp.single i 1 + Finsupp.single j 1).toMultiset
  simpa only [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul,
    Multiset.singleton_add] using hij

/-- Every real homogeneous degree-two polynomial is the diagonal of an actual
quadratic form, on the original algebraic coordinate space. -/
theorem quadraticForm_of_homogeneous_polynomial {σ : Type*}
    (P : MvPolynomial σ ℝ) (hP : P.IsHomogeneous 2) :
    ∃ Q : QuadraticForm ℝ (σ → ℝ), ∀ x, Q x = MvPolynomial.eval x P := by
  classical
  have hmon (d : σ →₀ ℕ) : ∃ Q : QuadraticForm ℝ (σ → ℝ),
      ∀ x, Q x = MvPolynomial.eval x (MvPolynomial.monomial d (P.coeff d)) := by
    by_cases hd : P.coeff d = 0
    · exact ⟨0, fun x => by simp [hd]⟩
    · have hdeg : d.degree = 2 := by
        simpa only [Finsupp.degree_eq_weight_one] using hP hd
      obtain ⟨i, j, hij⟩ := degree_two_eq_sum_single d hdeg
      refine ⟨P.coeff d • QuadraticMap.linMulLin
        (LinearMap.proj i) (LinearMap.proj j), ?_⟩
      intro x
      rw [hij, MvPolynomial.monomial_single_add]
      simp [MvPolynomial.monomial_eq, mul_comm, mul_assoc]
  choose q hq using hmon
  refine ⟨∑ d ∈ P.support, q d, ?_⟩
  intro x
  simp only [QuadraticMap.sum_apply, hq, MvPolynomial.eval_monomial]
  exact (MvPolynomial.eval_eq x P).symm

/-- The final conclusion of the algebraic extraction is an actual positive
definite real quadratic form, not only a predicate on polynomial coefficients. -/
theorem exists_posDef_quadraticForm_of_consecutive_even_powers
    {σ : Type*} {p : (σ → ℝ) → ℝ} {a : ℕ} (ha : 0 < a)
    (hscale : ∀ x : σ → ℝ, p (fun i => (2 : ℝ) * x i) = 2 * p x)
    (hpos : ∀ x : σ → ℝ, x ≠ 0 → 0 < p x)
    (hP : IsPolynomialFunction (fun x => p x ^ (2 * a)))
    (hQ : IsPolynomialFunction (fun x => p x ^ (2 * a + 2))) :
    ∃ Q : QuadraticForm ℝ (σ → ℝ), Q.PosDef ∧ ∀ x, Q x = p x ^ 2 := by
  obtain ⟨R, hRhom, hR, hRpos⟩ :=
    exists_positive_homogeneous_square_of_consecutive_even_powers ha hscale hpos hP hQ
  obtain ⟨Q, hQ⟩ := quadraticForm_of_homogeneous_polynomial R hRhom
  refine ⟨Q, ?_, fun x => (hQ x).trans (hR x)⟩
  intro x hx
  rw [hQ]
  exact hRpos x hx

end BanachIsometric
