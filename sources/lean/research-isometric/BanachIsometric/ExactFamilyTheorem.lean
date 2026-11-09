import BanachIsometric.ExactFamilyContinuousDegree
import BanachIsometric.ExactFamilyParity
import BanachIsometric.RadialStarBody

/-!
# Theorem 3.1 with its original normal-map regularity

The normal map is merely continuous. Its nonzero degree is the actual
continuous extension of the signed-fiber degree already proved. All signed
area, local-index, integrability, density and polynomiality steps are
discharged internally. The second endpoint uses the literal radial star
body and its proved equality with the infimum-defined Minkowski gauge.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory
open scoped NNReal

variable {m N : ℕ} [NeZero N]
  {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : EuclideanSpace ℝ (Fin m) → ℝ}
  (A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin N)) g p)

theorem exists_polynomial_power_of_nonzero_continuousNormalDegree
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hdegree : A.continuousNormalDegree e ≠ 0) (k : ℕ) :
    ∃ P : MvPolynomial (Fin m) ℝ, P.IsHomogeneous (N + 2 * k) ∧
      ∀ y : EuclideanSpace ℝ (Fin m),
        MvPolynomial.eval (fun j => y j) P = p y ^ (N + 2 * k) := by
  obtain ⟨P, hP⟩ := A.exists_polynomial_power_of_interior_counts μ hp hg hcont
    (A.continuousNormalDegree e) hdegree
    (fun y hy => A.ae_interior_body_count_eq_continuousNormalDegree μ e hg hcont hy) k
  let c := euclideanCoordinates m
  have hPc (x : Fin m → ℝ) : MvPolynomial.eval x P = p (c.symm x) ^ (N + 2 * k) := by
    have h := hP (c.symm x)
    change MvPolynomial.eval (c (c.symm x)) P = _ at h
    simpa only [c.apply_symm_apply] using h
  refine ⟨P, isHomogeneous_of_eval_two_mul P (N + 2 * k) ?_, hP⟩
  intro x
  rw [hPc, hPc]
  change p (c.symm ((2 : ℝ) • x)) ^ (N + 2 * k) = _
  rw [map_smul, hp.smul_nonneg 2 (by norm_num), mul_pow]

theorem exists_posDef_quadraticForm_of_nonzero_continuousNormalDegree
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hEven : Even N) (hdegree : A.continuousNormalDegree e ≠ 0) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧ ∀ y, Q y = p y ^ 2 := by
  apply A.exists_posDef_quadraticForm_of_interior_counts μ hp hg hcont hEven
    (A.continuousNormalDegree e) hdegree
  intro y hy
  exact A.ae_interior_body_count_eq_continuousNormalDegree μ e hg hcont hy

end BanachIsometric.ExactTangentialFamily

namespace BanachIsometric

open MeasureTheory
open scoped NNReal

/-- The coordinate form of the paper's full exact-family theorem, using a
literal star body with positive Lipschitz radial function. -/
theorem exactFamilyTheorem3_1 {m N : ℕ} [NeZero N]
    (K : RadialStarBody (EuclideanSpace ℝ (Fin N)))
    {p : EuclideanSpace ℝ (Fin m) → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    {C : ℝ≥0} (hK : LipschitzWith C K.radius)
    (A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin N)) K.gauge p)
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hEven : Even N) (hdegree : A.continuousNormalDegree e ≠ 0) :
    (∀ k : ℕ, ∃ P : MvPolynomial (Fin m) ℝ, P.IsHomogeneous (N + 2 * k) ∧
      ∀ y : EuclideanSpace ℝ (Fin m),
        MvPolynomial.eval (fun j => y j) P = p y ^ (N + 2 * k)) ∧
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧ ∀ y, Q y = p y ^ 2 := by
  obtain ⟨L, hL⟩ := K.exists_gauge_lipschitz hK
  exact ⟨fun k => A.exists_polynomial_power_of_nonzero_continuousNormalDegree
    μ e hp K.gauge_homogeneous hL.continuous hdegree k,
    A.exists_posDef_quadraticForm_of_nonzero_continuousNormalDegree
      μ e hp K.gauge_homogeneous hL.continuous hEven hdegree⟩

end BanachIsometric
