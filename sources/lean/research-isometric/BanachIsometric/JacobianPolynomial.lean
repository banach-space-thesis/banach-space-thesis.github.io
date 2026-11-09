import BanachIsometric.PolynomialIntegration
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The polynomial integrand in the signed degree calculation

Each Jacobian column is linear in the section vector. Its determinant has
degree equal to the real ambient dimension; the squared-length weight adds an
even degree. The evaluated formulas here are exact finite-coordinate formulas.
The signed area-degree identity and the analytic coefficient bounds are not
assumed to have been proved by constructing these polynomials.
-/

namespace BanachIsometric

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

noncomputable def coordinateLinearPolynomial (a : σ → ℝ) : MvPolynomial σ ℝ :=
  ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i

theorem eval_coordinateLinearPolynomial (a y : σ → ℝ) :
    MvPolynomial.eval y (coordinateLinearPolynomial a) = ∑ i, a i * y i := by
  classical
  simp [coordinateLinearPolynomial]

theorem coordinateLinearPolynomial_isHomogeneous (a : σ → ℝ) :
    (coordinateLinearPolynomial a).IsHomogeneous 1 := by
  classical
  exact MvPolynomial.IsHomogeneous.sum _ _ _
    (fun i _ => MvPolynomial.isHomogeneous_C_mul_X (a i) i)

noncomputable def squaredLengthPolynomial {N : ℕ} (A : Matrix (Fin N) σ ℝ) :
    MvPolynomial σ ℝ := ∑ i, coordinateLinearPolynomial (A i) ^ 2

theorem squaredLengthPolynomial_isHomogeneous {N : ℕ} (A : Matrix (Fin N) σ ℝ) :
    (squaredLengthPolynomial A).IsHomogeneous 2 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  simpa only [one_mul] using (coordinateLinearPolynomial_isHomogeneous (A i)).pow 2

noncomputable def jacobianDetPolynomial {N : ℕ}
    (D : Fin N → Matrix (Fin N) σ ℝ) : MvPolynomial σ ℝ :=
  Matrix.det (fun i j => coordinateLinearPolynomial (D j i))

theorem jacobianDetPolynomial_isHomogeneous {N : ℕ}
    (D : Fin N → Matrix (Fin N) σ ℝ) :
    (jacobianDetPolynomial D).IsHomogeneous N := by
  classical
  rw [jacobianDetPolynomial, Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro π _
  have hprod : (∏ i : Fin N, coordinateLinearPolynomial (D i (π i))).IsHomogeneous N := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 1)
      (fun i _ => coordinateLinearPolynomial_isHomogeneous (D i (π i)))
  simpa only [map_intCast] using hprod.C_mul (((Equiv.Perm.sign π : ℤ) : ℝ))

noncomputable def weightedJacobianPolynomial {N : ℕ} (k : ℕ)
    (A : Matrix (Fin N) σ ℝ) (D : Fin N → Matrix (Fin N) σ ℝ) :
    MvPolynomial σ ℝ := squaredLengthPolynomial A ^ k * jacobianDetPolynomial D

theorem weightedJacobianPolynomial_isHomogeneous {N : ℕ} (k : ℕ)
    (A : Matrix (Fin N) σ ℝ) (D : Fin N → Matrix (Fin N) σ ℝ) :
    (weightedJacobianPolynomial k A D).IsHomogeneous (N + 2 * k) := by
  simpa only [Nat.add_comm] using
    ((squaredLengthPolynomial_isHomogeneous A).pow k).mul
      (jacobianDetPolynomial_isHomogeneous D)

theorem eval_weightedJacobianPolynomial {N : ℕ} (k : ℕ)
    (A : Matrix (Fin N) σ ℝ) (D : Fin N → Matrix (Fin N) σ ℝ) (y : σ → ℝ) :
    MvPolynomial.eval y (weightedJacobianPolynomial k A D) =
      (∑ i : Fin N, (A.mulVec y i) ^ 2) ^ k *
        Matrix.det (fun i j => (D j).mulVec y i) := by
  classical
  simp only [weightedJacobianPolynomial, map_mul, map_pow, squaredLengthPolynomial,
    map_sum, jacobianDetPolynomial, RingHom.map_det, eval_coordinateLinearPolynomial]
  have hmat : (MvPolynomial.eval y).mapMatrix
      (fun i j => coordinateLinearPolynomial (D j i)) =
        (fun i j => (D j).mulVec y i) := by
    ext i j
    exact eval_coordinateLinearPolynomial (D j i) y
  rw [hmat]
  rfl

open MeasureTheory in
/-- Exact polynomiality of the integral of the coordinate Jacobian expression,
with its analytic coefficient-integrability obligation explicit. -/
theorem exists_homogeneous_weightedJacobian_integral
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {N : ℕ} (k : ℕ)
    (A : α → Matrix (Fin N) σ ℝ) (D : α → Fin N → Matrix (Fin N) σ ℝ)
    (hint : ∀ d : σ →₀ ℕ, d.degree = N + 2 * k →
      Integrable (fun x => (weightedJacobianPolynomial k (A x) (D x)).coeff d) μ) :
    ∃ Q : MvPolynomial σ ℝ, Q.IsHomogeneous (N + 2 * k) ∧
      ∀ y, MvPolynomial.eval y Q =
        ∫ x, (∑ i : Fin N, ((A x).mulVec y i) ^ 2) ^ k *
          Matrix.det (fun i j => (D x j).mulVec y i) ∂μ := by
  obtain ⟨Q, hQ, hval⟩ := exists_homogeneous_polynomial_integral μ
    (fun x => weightedJacobianPolynomial k (A x) (D x)) (N + 2 * k)
    (fun x => weightedJacobianPolynomial_isHomogeneous k (A x) (D x)) hint
  refine ⟨Q, hQ, ?_⟩
  intro y
  simpa only [eval_weightedJacobianPolynomial] using hval y

end BanachIsometric
