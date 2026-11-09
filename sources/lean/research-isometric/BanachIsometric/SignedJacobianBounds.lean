import BanachIsometric.JacobianPolynomial
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp

/-!
# Integrable coefficients of the actual weighted Jacobian polynomial

Coefficient functions are continuous finite sums and products in the operator
and its derivative. A Lipschitz operator family is bounded on a compact ball,
and its actual `fderiv` is measurable and bounded everywhere by the Lipschitz
constant. These facts discharge the coefficient-integrability premise.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped NNReal Topology BigOperators

noncomputable section

section CoefficientContinuity

variable {α σ : Type*} [TopologicalSpace α]

def ContinuousPolynomialCoefficients (P : α → MvPolynomial σ ℝ) : Prop :=
  ∀ d, Continuous (fun x ↦ (P x).coeff d)

namespace ContinuousPolynomialCoefficients

theorem constant (p : MvPolynomial σ ℝ) :
    ContinuousPolynomialCoefficients (fun _ : α ↦ p) := fun _ ↦ continuous_const

theorem mul {P Q : α → MvPolynomial σ ℝ}
    (hP : ContinuousPolynomialCoefficients P) (hQ : ContinuousPolynomialCoefficients Q) :
    ContinuousPolynomialCoefficients (fun x ↦ P x * Q x) := by
  classical
  intro d
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finset_sum _ (fun e _ ↦ (hP e.1).mul (hQ e.2))

theorem pow {P : α → MvPolynomial σ ℝ} (hP : ContinuousPolynomialCoefficients P) (n : ℕ) :
    ContinuousPolynomialCoefficients (fun x ↦ P x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using constant (α := α) (1 : MvPolynomial σ ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul hP

theorem sum {ι : Type*} (s : Finset ι) (P : ι → α → MvPolynomial σ ℝ)
    (hP : ∀ i ∈ s, ContinuousPolynomialCoefficients (P i)) :
    ContinuousPolynomialCoefficients (fun x ↦ ∑ i ∈ s, P i x) := by
  intro d
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finset_sum _ (fun i hi ↦ hP i hi d)

theorem prod {ι : Type*} (s : Finset ι) (P : ι → α → MvPolynomial σ ℝ)
    (hP : ∀ i ∈ s, ContinuousPolynomialCoefficients (P i)) :
    ContinuousPolynomialCoefficients (fun x ↦ ∏ i ∈ s, P i x) := by
  classical
  revert hP
  induction s using Finset.induction_on with
  | empty => intro _; simpa only [Finset.prod_empty] using constant (α := α) (1 : MvPolynomial σ ℝ)
  | @insert i s hi ih =>
    intro hP
    simpa only [Finset.prod_insert hi] using
      (hP i (Finset.mem_insert_self i s)).mul (ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)))

theorem C_mul {P : α → MvPolynomial σ ℝ} {a : α → ℝ}
    (hP : ContinuousPolynomialCoefficients P) (ha : Continuous a) :
    ContinuousPolynomialCoefficients (fun x ↦ MvPolynomial.C (a x) * P x) := by
  intro d
  simpa only [MvPolynomial.coeff_C_mul] using ha.mul (hP d)

end ContinuousPolynomialCoefficients

variable [Fintype σ]

theorem continuous_coeff_coordinateLinearPolynomial (a : α → σ → ℝ)
    (ha : ∀ i, Continuous (fun x ↦ a x i)) :
    ContinuousPolynomialCoefficients (fun x ↦ coordinateLinearPolynomial (a x)) := by
  classical
  apply ContinuousPolynomialCoefficients.sum
  intro i _
  exact (ContinuousPolynomialCoefficients.constant (MvPolynomial.X i)).C_mul (ha i)

theorem continuous_coeff_squaredLengthPolynomial {N : ℕ} (A : α → Matrix (Fin N) σ ℝ)
    (hA : ∀ i j, Continuous (fun x ↦ A x i j)) :
    ContinuousPolynomialCoefficients (fun x ↦ squaredLengthPolynomial (A x)) := by
  apply ContinuousPolynomialCoefficients.sum
  intro i _
  exact (continuous_coeff_coordinateLinearPolynomial _ (hA i)).pow 2

theorem continuous_coeff_jacobianDetPolynomial {N : ℕ}
    (D : α → Fin N → Matrix (Fin N) σ ℝ)
    (hD : ∀ j i l, Continuous (fun x ↦ D x j i l)) :
    ContinuousPolynomialCoefficients (fun x ↦ jacobianDetPolynomial (D x)) := by
  classical
  simp only [jacobianDetPolynomial, Matrix.det_apply']
  apply ContinuousPolynomialCoefficients.sum
  intro π _
  have hprod := ContinuousPolynomialCoefficients.prod Finset.univ
    (fun i x ↦ coordinateLinearPolynomial (D x i (π i)))
    (fun i _ ↦ continuous_coeff_coordinateLinearPolynomial _ (hD i (π i)))
  simpa only [map_intCast] using hprod.C_mul
    (continuous_const : Continuous (fun _ : α ↦ ((Equiv.Perm.sign π : ℤ) : ℝ)))

theorem continuous_coeff_weightedJacobianPolynomial {N : ℕ} (k : ℕ)
    (A : α → Matrix (Fin N) σ ℝ) (D : α → Fin N → Matrix (Fin N) σ ℝ)
    (hA : ∀ i j, Continuous (fun x ↦ A x i j))
    (hD : ∀ j i l, Continuous (fun x ↦ D x j i l)) :
    ContinuousPolynomialCoefficients (fun x ↦ weightedJacobianPolynomial k (A x) (D x)) :=
  ((continuous_coeff_squaredLengthPolynomial A hA).pow k).mul
    (continuous_coeff_jacobianDetPolynomial D hD)

end CoefficientContinuity

section BoundedComposition

variable {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem integrable_continuous_comp_of_ae_bounded
    (μ : Measure α) [IsFiniteMeasure μ] {g : α → V} (hg : Measurable g)
    {R : ℝ} (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ R) {H : V → ℝ} (hH : Continuous H) :
    Integrable (fun x ↦ H (g x)) μ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) R).bddAbove_image hH.norm.continuousOn
  apply (integrable_const B).mono' (hH.measurable.comp hg).aestronglyMeasurable
  filter_upwards [hbound] with x hx
  exact hB (mem_image_of_mem (fun z ↦ ‖H z‖)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx))

end BoundedComposition

section ActualOperators

variable {σ : Type*} [Fintype σ] {N : ℕ}

def operatorCoordinateMatrix
    (A : EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)) : Matrix (Fin N) σ ℝ :=
  fun i j ↦ A (EuclideanSpace.basisFun σ ℝ j) i

def operatorDerivativeCoordinates
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ]
      (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N))) :
    Fin N → Matrix (Fin N) σ ℝ :=
  fun j ↦ operatorCoordinateMatrix (D (EuclideanSpace.basisFun (Fin N) ℝ j))

@[fun_prop]
theorem continuous_operatorCoordinateMatrix : Continuous
    (operatorCoordinateMatrix : (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)) →
      Matrix (Fin N) σ ℝ) := by
  unfold operatorCoordinateMatrix
  fun_prop

@[fun_prop]
theorem continuous_operatorDerivativeCoordinates : Continuous
    (operatorDerivativeCoordinates :
      (EuclideanSpace ℝ (Fin N) →L[ℝ] (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N))) →
      Fin N → Matrix (Fin N) σ ℝ) := by
  unfold operatorDerivativeCoordinates
  fun_prop

theorem continuous_actual_weightedJacobian_coeff (k : ℕ) (d : σ →₀ ℕ) :
    Continuous (fun z : (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)) ×
      (EuclideanSpace ℝ (Fin N) →L[ℝ] (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N))) ↦
      (weightedJacobianPolynomial k (operatorCoordinateMatrix z.1)
        (operatorDerivativeCoordinates z.2)).coeff d) := by
  apply continuous_coeff_weightedJacobianPolynomial
  · intro i j
    fun_prop
  · intro j i l
    fun_prop

set_option maxHeartbeats 200000 in
/-- Every coefficient of the actual polynomial built from `A` and its actual
Fréchet derivative is integrable on a measurable bounded domain. No analytic
coefficient-integrability premise is retained. -/
theorem integrableOn_actual_weightedJacobian_coeff
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [IsFiniteMeasureOnCompacts μ]
    (A : EuclideanSpace ℝ (Fin N) →
      (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)))
    {L : ℝ≥0} (hA : LipschitzWith L A) {Ω : Set (EuclideanSpace ℝ (Fin N))}
    (hΩ : MeasurableSet Ω) {R : ℝ} (hΩR : Ω ⊆ Metric.closedBall 0 R)
    (k : ℕ) (d : σ →₀ ℕ) :
    IntegrableOn (fun x ↦ (weightedJacobianPolynomial k (operatorCoordinateMatrix (A x))
      (operatorDerivativeCoordinates (fderiv ℝ A x))).coeff d) Ω μ := by
  let V := (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)) ×
    (EuclideanSpace ℝ (Fin N) →L[ℝ] (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)))
  let H : V → ℝ := fun z ↦ (weightedJacobianPolynomial k (operatorCoordinateMatrix z.1)
    (operatorDerivativeCoordinates z.2)).coeff d
  letI : FiniteDimensional ℝ (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
  letI : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin N) →L[ℝ]
    (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N))) := inferInstance
  letI : ProperSpace (EuclideanSpace ℝ (Fin N) →L[ℝ]
    (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N))) :=
    FiniteDimensional.proper ℝ (EuclideanSpace ℝ (Fin N) →L[ℝ]
      (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)))
  borelize (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N))
  borelize (EuclideanSpace ℝ (Fin N) →L[ℝ]
    (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)))
  haveI : IsFiniteMeasure (μ.restrict Ω) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      lt_of_le_of_lt (measure_mono hΩR) (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) R).measure_lt_top⟩
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) R).bddAbove_image
    hA.continuous.norm.continuousOn
  let g : EuclideanSpace ℝ (Fin N) → V := fun x ↦ (A x, fderiv ℝ A x)
  have hg : Measurable g := hA.continuous.measurable.prodMk (measurable_fderiv ℝ A)
  let K : Set V := Metric.closedBall (0 : EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N)) B ×ˢ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin N) →L[ℝ]
      (EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ (Fin N))) (L : ℝ)
  have hK : IsCompact K := (isCompact_closedBall _ B).prod (isCompact_closedBall _ (L : ℝ))
  have hbound : ∀ᵐ x ∂μ.restrict Ω, g x ∈ K := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    constructor
    · simpa only [Metric.mem_closedBall, dist_zero_right] using
        hB (mem_image_of_mem (fun x ↦ ‖A x‖) (hΩR hx))
    · change fderiv ℝ A x ∈ Metric.closedBall 0 (L : ℝ)
      rw [Metric.mem_closedBall]
      change ‖fderiv ℝ A x - 0‖ ≤ (L : ℝ)
      have hzero : fderiv ℝ A x - 0 = fderiv ℝ A x := by
        ext v y i
        simp
      rw [hzero]
      exact norm_fderiv_le_of_lipschitz ℝ hA
  have hH : Continuous H := continuous_actual_weightedJacobian_coeff k d
  obtain ⟨Bcoeff, hBcoeff⟩ := hK.bddAbove_image hH.norm.continuousOn
  change Integrable (fun x ↦ H (g x)) (μ.restrict Ω)
  apply (integrable_const Bcoeff).mono' (hH.measurable.comp hg).aestronglyMeasurable
  filter_upwards [hbound] with x hx
  exact hBcoeff (mem_image_of_mem (fun z ↦ ‖H z‖) hx)

end ActualOperators

end

end BanachIsometric
