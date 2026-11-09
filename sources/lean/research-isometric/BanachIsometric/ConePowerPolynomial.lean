import BanachIsometric.ExactFamilyPolynomial
import BanachIsometric.GaugeLevelGeometry
import BanachIsometric.SignedBodyIntegral
import BanachIsometric.EuclideanPolynomialQuadratic

/-!
# From actual interior counts to polynomial powers and a quadratic form

This assembles the signed area formula, actual cone polynomial, body scaling,
positive moment constants, and algebraic extraction on the original Euclidean
model. The interior-count hypothesis here is the intermediate interface; its
discharge from the actual normal-cone index is proved separately.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped Topology NNReal

namespace ExactTangentialFamily

variable {m N : ℕ} [NeZero N]
  {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : EuclideanSpace ℝ (Fin m) → ℝ}
  (A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin N)) g p)

theorem exists_polynomial_power_of_interior_counts
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (D : ℤ) (hD : D ≠ 0)
    (hcount : ∀ y, 0 < p y → ∀ᵐ v ∂μ, v ∈ interior {v | g v ≤ p y} →
      signedFiberCount (A.coneEvaluation y) (fderiv ℝ (A.coneEvaluation y))
        (Metric.closedBall 0 1) v = D) (k : ℕ) :
    ∃ P : MvPolynomial (Fin m) ℝ, ∀ y : EuclideanSpace ℝ (Fin m),
      MvPolynomial.eval (fun j => y j) P = p y ^ (N + 2 * k) := by
  obtain ⟨L, hL⟩ := A.exists_lipschitz_operator_cone
  obtain ⟨Q, hQhom, hQ⟩ := exists_homogeneous_actual_weightedJacobian_integral μ
    (coneExtension A.maps) hL (Ω := Metric.closedBall 0 1)
    Metric.isClosed_closedBall.measurableSet (R := 1) Subset.rfl k
  let M : ℝ := ∫ v in {v | g v ≤ 1}, ‖v‖ ^ (2 * k) ∂μ
  let c : ℝ := (D : ℝ) * M
  have hM : 0 < M := integral_norm_pow_unit_sublevel_pos μ hg hcont (2 * k)
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hc : c ≠ 0 := mul_ne_zero hDR hM.ne'
  refine ⟨MvPolynomial.C c⁻¹ * Q, fun y => ?_⟩
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  by_cases hy : y = 0
  · subst y
    have hdegree : N + 2 * k ≠ 0 := by have := NeZero.ne N; omega
    have hcoeff : Q.coeff 0 = 0 := by
      by_contra hne
      have hdeg : (0 : ℕ) = N + 2 * k := by simpa using hQhom hne
      exact hdegree hdeg.symm
    have hzero : MvPolynomial.eval (0 : Fin m → ℝ) Q = 0 := by
      rw [MvPolynomial.eval_zero]
      exact hcoeff
    have hpzero : p 0 = 0 := (hp.eq_zero_iff 0).mpr rfl
    change c⁻¹ * MvPolynomial.eval (0 : Fin m → ℝ) Q = p 0 ^ (N + 2 * k)
    rw [hzero, hpzero, zero_pow hdegree, mul_zero]
  · have hpy : 0 < p y := hp.pos hy
    obtain ⟨Ly, hLy⟩ := A.exists_lipschitz_coneEvaluation y
    have himage : A.coneEvaluation y '' Metric.closedBall 0 1 ⊆ {v | g v ≤ p y} := by
      rintro _ ⟨x, hx, rfl⟩
      have hxn : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      rw [mem_setOf_eq, A.gauge_coneEvaluation hg]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hxn hpy.le
    have hbody := integral_signedJacobian_eq_body_integral_of_interior_count μ hLy
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)
      (isClosed_le hcont continuous_const).measurableSet
      (measure_frontier_pos_sublevel_eq_zero μ hg hcont hpy) himage D (hcount y hpy)
      (continuous_norm.pow (2 * k))
    have hval : MvPolynomial.eval (fun j => y j) Q =
        ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1,
          ‖A.coneEvaluation y x‖ ^ (2 * k) * (fderiv ℝ (A.coneEvaluation y) x).det ∂μ := hQ y
    have heq : MvPolynomial.eval (fun j => y j) Q = c * p y ^ (N + 2 * k) := by
      rw [hval]
      calc
        (∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1,
            ‖A.coneEvaluation y x‖ ^ (2 * k) * (fderiv ℝ (A.coneEvaluation y) x).det ∂μ) =
            (D : ℝ) * ∫ v in {v | g v ≤ p y}, ‖v‖ ^ (2 * k) ∂μ := by
          simpa only [mul_comm] using hbody
        _ = c * p y ^ (N + 2 * k) := by
          rw [integral_norm_pow_pos_sublevel μ hg (2 * k) hpy, finrank_euclideanSpace_fin]
          dsimp [c, M]
          ring
    rw [heq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem exists_posDef_quadraticForm_of_interior_counts
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hEven : Even N) (D : ℤ) (hD : D ≠ 0)
    (hcount : ∀ y, 0 < p y → ∀ᵐ v ∂μ, v ∈ interior {v | g v ≤ p y} →
      signedFiberCount (A.coneEvaluation y) (fderiv ℝ (A.coneEvaluation y))
        (Metric.closedBall 0 1) v = D) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧ ∀ y, Q y = p y ^ 2 := by
  obtain ⟨a, ha⟩ := hEven
  have hNa : N = 2 * a := by omega
  have haPos : 0 < a := by have := NeZero.ne N; omega
  obtain ⟨P, hP⟩ := A.exists_polynomial_power_of_interior_counts μ hp hg hcont D hD hcount 0
  obtain ⟨Q, hQ⟩ := A.exists_polynomial_power_of_interior_counts μ hp hg hcont D hD hcount 1
  apply exists_posDef_euclidean_quadraticForm_of_consecutive_even_powers hp haPos
  · exact ⟨P, fun y => by simpa only [hNa, mul_zero, add_zero] using hP y⟩
  · exact ⟨Q, fun y => by simpa only [hNa, mul_one] using hQ y⟩

end ExactTangentialFamily

end BanachIsometric
