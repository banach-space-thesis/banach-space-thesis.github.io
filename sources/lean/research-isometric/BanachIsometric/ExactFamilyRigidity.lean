import BanachIsometric.ConePowerPolynomial
import BanachIsometric.ExactFamilyBodyCount

/-!
# The analytic exact-family rigidity theorem

A nonzero actual normal-cone signed index gives all the required polynomial
powers, hence an actual positive-definite quadratic form with diagonal p².
There is no signed-degree formula, integrability, finite-fiber, polynomiality,
or density-constancy premise. Those steps are proved in the imported chain.

Alternative route: actual signed fiber counts construct the local index;
Piola, divergence and actual mollification prove its homotopy invariance.
Positive-parallel and orthogonal homotopies compare F_y with the normal cone,
avoiding a degree-composition/radial-orientation black box. We integrate on the
closed unit ball; its actual image and fiber counts give the body integral.
The nonzero-index exact family must still be constructed from bundle data.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory
open scoped Topology NNReal

variable {m N : ℕ} [NeZero N]
  {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : EuclideanSpace ℝ (Fin m) → ℝ}
  (A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin N)) g p)

theorem exists_polynomial_power_of_nonzero_normalConeSignedIndex
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    (hindex : A.normalConeSignedIndex e ≠ 0) (k : ℕ) :
    ∃ P : MvPolynomial (Fin m) ℝ, ∀ y : EuclideanSpace ℝ (Fin m),
      MvPolynomial.eval (fun j => y j) P = p y ^ (N + 2 * k) := by
  apply A.exists_polynomial_power_of_interior_counts μ hp hg hcont
    (A.normalConeSignedIndex e) hindex
  intro y hy
  exact A.ae_interior_body_coneEvaluation_count_eq_normalConeSignedIndex μ e hg hcont hy hnormal

theorem exists_posDef_quadraticForm_of_nonzero_normalConeSignedIndex
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hEven : Even N)
    (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    (hindex : A.normalConeSignedIndex e ≠ 0) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧ ∀ y, Q y = p y ^ 2 := by
  apply A.exists_posDef_quadraticForm_of_interior_counts μ hp hg hcont hEven
    (A.normalConeSignedIndex e) hindex
  intro y hy
  exact A.ae_interior_body_coneEvaluation_count_eq_normalConeSignedIndex μ e hg hcont hy hnormal

end BanachIsometric.ExactTangentialFamily
