import BanachIsometric.SignedJacobianBounds
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Determinant
import BanachIsometric.ConeGeometry

/-!
# The actual polynomial on the analytic side of the exact-family argument

Rademacher's theorem is applied once to the operator-valued family. Outside
one common measurable null set, evaluation at every section vector commutes
with the derivative. The coefficient bounds are discharged, so the actual
weighted signed Jacobian integral is a homogeneous polynomial in that vector.
The signed area/degree identity remains a separate theorem.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped NNReal Topology BigOperators

noncomputable section

variable {σ : Type*} [Fintype σ] {N : ℕ}

theorem operatorCoordinateMatrix_mulVec
    (A : EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ σ) :
    (operatorCoordinateMatrix A).mulVec (fun j ↦ y j) = fun i ↦ A y i := by
  classical
  have hy : (∑ j, y j • EuclideanSpace.basisFun σ ℝ j) = y := by
    simpa only [EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun σ ℝ).sum_repr y
  funext i
  calc
    (operatorCoordinateMatrix A).mulVec (fun j ↦ y j) i =
        A (∑ j, y j • EuclideanSpace.basisFun σ ℝ j) i := by
      change (∑ j, A (EuclideanSpace.basisFun σ ℝ j) i * y j) =
        (EuclideanSpace.proj i) (A (∑ j, y j • EuclideanSpace.basisFun σ ℝ j))
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, map_smul]
      exact mul_comm _ _
    _ = A y i := by rw [hy]

theorem det_operatorCoordinateMatrix
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    Matrix.det (operatorCoordinateMatrix D) = LinearMap.det D.toLinearMap := by
  classical
  have hmatrix : operatorCoordinateMatrix D = LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis D.toLinearMap := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    rfl
  rw [hmatrix, LinearMap.det_toMatrix]

/-- One measurable null set works for every vector parameter, including
uncountably many of them. It is obtained from differentiability of `A` itself. -/
theorem exists_common_null_set_operatorFamily_derivative
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (A : EuclideanSpace ℝ (Fin N) →
      (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)))
    {L : ℝ≥0} (hA : LipschitzWith L A) :
    ∃ Z : Set (EuclideanSpace ℝ (Fin N)), MeasurableSet Z ∧ μ Z = 0 ∧
      (∀ x ∉ Z, HasFDerivAt A (fderiv ℝ A x) x ∧
        ∀ y : EuclideanSpace ℝ σ,
          HasFDerivAt (fun z ↦ A z y)
            ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) y).comp (fderiv ℝ A x)) x ∧
          ∀ v, fderiv ℝ (fun z ↦ A z y) x v = fderiv ℝ A x v y) := by
  let Z : Set (EuclideanSpace ℝ (Fin N)) := {x | ¬ DifferentiableAt ℝ A x}
  have hZ : MeasurableSet Z := (measurableSet_of_differentiableAt ℝ A).compl
  have hnull : μ Z = 0 := (ae_iff).mp hA.ae_differentiableAt
  refine ⟨Z, hZ, hnull, ?_⟩
  intro x hx
  have hAx : DifferentiableAt ℝ A x := by simpa only [Z, mem_setOf_eq, not_not] using hx
  refine ⟨hAx.hasFDerivAt, ?_⟩
  intro y
  have hEval : HasFDerivAt (fun z ↦ A z y)
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) y).comp (fderiv ℝ A x)) x :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) y).hasFDerivAt.comp x hAx.hasFDerivAt
  refine ⟨hEval, ?_⟩
  intro v
  rw [hEval.fderiv]
  rfl

theorem eval_actual_weightedJacobian_eq
    (A : EuclideanSpace ℝ (Fin N) →
      (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)))
    {x : EuclideanSpace ℝ (Fin N)} (hAx : DifferentiableAt ℝ A x)
    (k : ℕ) (y : EuclideanSpace ℝ σ) :
    MvPolynomial.eval (fun j ↦ y j)
      (weightedJacobianPolynomial k (operatorCoordinateMatrix (A x))
        (operatorDerivativeCoordinates (fderiv ℝ A x))) =
      ‖A x y‖ ^ (2 * k) * LinearMap.det (fderiv ℝ (fun z ↦ A z y) x).toLinearMap := by
  classical
  have hEval : HasFDerivAt (fun z ↦ A z y)
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) y).comp (fderiv ℝ A x)) x :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) y).hasFDerivAt.comp x hAx.hasFDerivAt
  have hmatrix : (fun i j ↦ (operatorDerivativeCoordinates (fderiv ℝ A x) j).mulVec (fun l ↦ y l) i) =
      operatorCoordinateMatrix (fderiv ℝ (fun z ↦ A z y) x) := by
    ext i j
    change (operatorCoordinateMatrix (fderiv ℝ A x (EuclideanSpace.basisFun (Fin N) ℝ j))).mulVec
      (fun l ↦ y l) i = _
    rw [operatorCoordinateMatrix_mulVec, hEval.fderiv]
    rfl
  have hnorm : (∑ i : Fin N, (A x y i) ^ 2) = ‖A x y‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq (A x y)).symm
  rw [eval_weightedJacobianPolynomial, operatorCoordinateMatrix_mulVec, hmatrix,
    det_operatorCoordinateMatrix, hnorm, ← pow_mul]

/-- The signed Jacobian integrand is genuinely integrable, rather than merely
having a Bochner integral whose default value could mask nonintegrability. -/
theorem integrableOn_actual_weightedJacobian_integrand
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (A : EuclideanSpace ℝ (Fin N) →
      (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)))
    {L : ℝ≥0} (hA : LipschitzWith L A) {Ω : Set (EuclideanSpace ℝ (Fin N))}
    (hΩ : MeasurableSet Ω) {R : ℝ} (hΩR : Ω ⊆ Metric.closedBall 0 R)
    (k : ℕ) (y : EuclideanSpace ℝ σ) :
    IntegrableOn (fun x ↦ ‖A x y‖ ^ (2 * k) *
      LinearMap.det (fderiv ℝ (fun z ↦ A z y) x).toLinearMap) Ω μ := by
  let P := fun x ↦ weightedJacobianPolynomial k (operatorCoordinateMatrix (A x))
    (operatorDerivativeCoordinates (fderiv ℝ A x))
  have hhom : ∀ x, (P x).IsHomogeneous (N + 2 * k) :=
    fun x ↦ weightedJacobianPolynomial_isHomogeneous k _ _
  have hsupport : ∀ x, (P x).support ⊆ homogeneousMonomials σ (N + 2 * k) := by
    intro x d hd
    apply (mem_homogeneousMonomials _ d).mpr
    simpa only [Finsupp.degree_eq_weight_one] using (hhom x) (MvPolynomial.mem_support_iff.mp hd)
  have hint : ∀ d ∈ homogeneousMonomials σ (N + 2 * k),
      Integrable (fun x ↦ (P x).coeff d) (μ.restrict Ω) :=
    fun d _ ↦ integrableOn_actual_weightedJacobian_coeff μ A hA hΩ hΩR k d
  have hEval := integrable_eval_of_integrable_coefficients (μ.restrict Ω)
    (homogeneousMonomials σ (N + 2 * k)) P hsupport hint (fun j ↦ y j)
  apply hEval.congr
  filter_upwards [ae_restrict_of_ae (hA.ae_differentiableAt (μ := μ))] with x hx
  exact eval_actual_weightedJacobian_eq A hx k y

/-- The genuine analytic polynomial integral in Theorem 3.1. All coefficient
integrability hypotheses have been proved from the Lipschitz family and a
bounded measurable domain. The determinant is the actual Fréchet Jacobian of
`x ↦ A(x)y`, not an independently supplied matrix family. -/
theorem exists_homogeneous_actual_weightedJacobian_integral
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (A : EuclideanSpace ℝ (Fin N) →
      (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)))
    {L : ℝ≥0} (hA : LipschitzWith L A) {Ω : Set (EuclideanSpace ℝ (Fin N))}
    (hΩ : MeasurableSet Ω) {R : ℝ} (hΩR : Ω ⊆ Metric.closedBall 0 R) (k : ℕ) :
    ∃ Q : MvPolynomial σ ℝ, Q.IsHomogeneous (N + 2 * k) ∧
      ∀ y : EuclideanSpace ℝ σ, MvPolynomial.eval (fun j ↦ y j) Q =
        ∫ x in Ω, ‖A x y‖ ^ (2 * k) * LinearMap.det (fderiv ℝ (fun z ↦ A z y) x).toLinearMap ∂μ := by
  obtain ⟨Q, hQ, hval⟩ := exists_homogeneous_weightedJacobian_integral (μ.restrict Ω) k
    (fun x ↦ operatorCoordinateMatrix (A x))
    (fun x ↦ operatorDerivativeCoordinates (fderiv ℝ A x))
    (fun d _ ↦ integrableOn_actual_weightedJacobian_coeff μ A hA hΩ hΩR k d)
  refine ⟨Q, hQ, ?_⟩
  intro y
  rw [hval]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (hA.ae_differentiableAt (μ := μ))] with x hx
  exact (eval_weightedJacobianPolynomial k _ _ (fun j ↦ y j)).symm.trans
    (eval_actual_weightedJacobian_eq A hx k y)

/-- Direct exact-family form on the open unit ball. The global operator
Lipschitz property of the cone is derived from the sphere data here. -/
theorem ExactTangentialFamily.exists_homogeneous_coneEvaluation_integral
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : EuclideanSpace ℝ σ → ℝ}
    (A : ExactTangentialFamily (EuclideanSpace ℝ σ) (EuclideanSpace ℝ (Fin N)) g p)
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure] (k : ℕ) :
    ∃ Q : MvPolynomial σ ℝ, Q.IsHomogeneous (N + 2 * k) ∧
      ∀ y : EuclideanSpace ℝ σ, MvPolynomial.eval (fun j ↦ y j) Q =
        ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1,
          ‖A.coneEvaluation y x‖ ^ (2 * k) *
            LinearMap.det (fderiv ℝ (A.coneEvaluation y) x).toLinearMap ∂μ := by
  obtain ⟨L, hL⟩ := A.exists_lipschitz_operator_cone
  obtain ⟨Q, hQ, hval⟩ := exists_homogeneous_actual_weightedJacobian_integral μ
    (coneExtension A.maps) hL (Ω := Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)
    Metric.isOpen_ball.measurableSet (R := 1) Metric.ball_subset_closedBall k
  refine ⟨Q, hQ, ?_⟩
  intro y
  simpa only [ExactTangentialFamily.coneEvaluation] using hval y

end

end BanachIsometric
