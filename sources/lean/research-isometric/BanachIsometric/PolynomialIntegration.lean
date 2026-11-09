import BanachIsometric.PolynomialRigidity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Vector

/-!
# Coefficientwise integration of a polynomial family

This proves the finite-sum integration step on the left side of the signed
degree identity. The signed area-degree identity itself is not a hypothesis
disguised by this construction: it remains a separate outstanding theorem.
-/

namespace BanachIsometric

open MeasureTheory

variable {α σ : Type*} [MeasurableSpace α]

/-- The coefficientwise integral over a specified common finite support. -/
noncomputable def polynomialIntegral (μ : Measure α) (s : Finset (σ →₀ ℕ))
    (P : α → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ d ∈ s, MvPolynomial.monomial d (∫ x, (P x).coeff d ∂μ)

private theorem eval_eq_sum_of_support_subset
    (P : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)) (hs : P.support ⊆ s) (y : σ → ℝ) :
    MvPolynomial.eval y P = ∑ d ∈ s, P.coeff d * d.prod (fun i e => y i ^ e) := by
  classical
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_subset hs
  intro d _ hd
  rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul]

/-- Evaluation of the coefficientwise integral is precisely the integral of
the evaluated polynomial. Integrability of every required coefficient and a
common finite support are explicit, rather than inferred from pointwise
polynomiality alone. -/
theorem eval_polynomialIntegral (μ : Measure α) (s : Finset (σ →₀ ℕ))
    (P : α → MvPolynomial σ ℝ) (hs : ∀ x, (P x).support ⊆ s)
    (hint : ∀ d ∈ s, Integrable (fun x => (P x).coeff d) μ) (y : σ → ℝ) :
    MvPolynomial.eval y (polynomialIntegral μ s P) =
      ∫ x, MvPolynomial.eval y (P x) ∂μ := by
  classical
  simp only [polynomialIntegral, map_sum, MvPolynomial.eval_monomial]
  simp_rw [eval_eq_sum_of_support_subset _ s (hs _) y]
  rw [integral_finset_sum s (fun d hd => (hint d hd).mul_const _)]
  apply Finset.sum_congr rfl
  intro d _
  exact (integral_mul_const _ _).symm

theorem integrable_eval_of_integrable_coefficients
    (μ : Measure α) (s : Finset (σ →₀ ℕ)) (P : α → MvPolynomial σ ℝ)
    (hs : ∀ x, (P x).support ⊆ s)
    (hint : ∀ d ∈ s, Integrable (fun x => (P x).coeff d) μ) (y : σ → ℝ) :
    Integrable (fun x => MvPolynomial.eval y (P x)) μ := by
  classical
  simp_rw [eval_eq_sum_of_support_subset _ s (hs _) y]
  exact integrable_finset_sum s (fun d hd => (hint d hd).mul_const _)

/-- Homogeneous degree is retained, including the possibility that all
integrated coefficients cancel. No nonzero-integral premise is needed. -/
theorem polynomialIntegral_isHomogeneous
    (μ : Measure α) (s : Finset (σ →₀ ℕ)) (P : α → MvPolynomial σ ℝ)
    (n : ℕ) (hP : ∀ x, (P x).IsHomogeneous n) :
    (polynomialIntegral μ s P).IsHomogeneous n := by
  classical
  apply MvPolynomial.IsHomogeneous.sum s _ n
  intro d _
  by_cases hd : d.degree = n
  · exact MvPolynomial.isHomogeneous_monomial _ hd
  · have hz : ∀ x, (P x).coeff d = 0 := by
      intro x
      exact (hP x).coeff_eq_zero hd
    simp only [hz, integral_zero, MvPolynomial.monomial_zero]
    exact (MvPolynomial.homogeneousSubmodule σ ℝ n).zero_mem

section FiniteVariables

variable [Fintype σ]

/-- All monomials of a prescribed homogeneous degree form an actual finite
set, via the equivalence with the finite symmetric power of the variable set. -/
noncomputable def homogeneousMonomials (σ : Type*) [Fintype σ] (n : ℕ) :
    Finset (σ →₀ ℕ) := by
  classical
  exact Finset.univ.image (fun s : Sym σ n => (Sym.equivNatSum σ n s).val)

theorem mem_homogeneousMonomials (n : ℕ) (d : σ →₀ ℕ) :
    d ∈ homogeneousMonomials σ n ↔ d.degree = n := by
  classical
  constructor
  · intro hd
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hd
    simpa only [Finsupp.sum, Finsupp.degree] using (Sym.equivNatSum σ n s).property
  · intro hd
    let d' : {P : σ →₀ ℕ // P.sum (fun _ => id) = n} :=
      ⟨d, by simpa only [Finsupp.sum, Finsupp.degree] using hd⟩
    apply Finset.mem_image.mpr
    refine ⟨(Sym.equivNatSum σ n).symm d', Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((Sym.equivNatSum σ n).apply_symm_apply d')

/-- In finitely many variables, homogeneous polynomial families automatically
have one finite common support. Thus coefficientwise integration preserves
pointwise polynomiality and homogeneous degree, with the exact integral as
the resulting polynomial's value. -/
theorem exists_homogeneous_polynomial_integral
    (μ : Measure α) (P : α → MvPolynomial σ ℝ) (n : ℕ)
    (hP : ∀ x, (P x).IsHomogeneous n)
    (hint : ∀ d : σ →₀ ℕ, d.degree = n → Integrable (fun x => (P x).coeff d) μ) :
    ∃ Q : MvPolynomial σ ℝ, Q.IsHomogeneous n ∧
      ∀ y, MvPolynomial.eval y Q = ∫ x, MvPolynomial.eval y (P x) ∂μ := by
  classical
  refine ⟨polynomialIntegral μ (homogeneousMonomials σ n) P,
    polynomialIntegral_isHomogeneous μ _ P n hP, ?_⟩
  intro y
  apply eval_polynomialIntegral
  · intro x d hd
    apply (mem_homogeneousMonomials n d).mpr
    have hnz := MvPolynomial.mem_support_iff.mp hd
    simpa only [Finsupp.degree_eq_weight_one] using (hP x) hnz
  · intro d hd
    exact hint d ((mem_homogeneousMonomials n d).mp hd)

end FiniteVariables

end BanachIsometric
