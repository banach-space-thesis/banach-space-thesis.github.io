import BanachIsometric.ComplexFunctionalGeometry

/-!
# Concrete complex geometric setup from Theorem A's original hypotheses

An arbitrary algebraic `(n+1)`-dimensional complex subspace acquires genuine
Hermitian coordinates with global gauge regularity. In those coordinates the
actual principal exact-section data are constructed. The analytic/topological
argument proving quadraticity is a separate obligation, not a field here.
-/

namespace BanachIsometric

open MeasureTheory
open scoped NNReal

noncomputable section

section AlgebraicPullback

variable {X W : Type*} [AddCommGroup X] [Module ℂ X]
  [AddCommGroup W] [Module ℂ W]

theorem IsDefiniteComplexHomogeneous.pullback {p : X → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) (j : W →ₗ[ℂ] X) (hj : Function.Injective j) :
    IsDefiniteComplexHomogeneous (fun w => p (j w)) where
  nonneg := fun w => hp.nonneg (j w)
  eq_zero_iff := fun w => by
    rw [hp.eq_zero_iff]
    exact ⟨fun h => hj (h.trans j.map_zero.symm), fun h => by rw [h, j.map_zero]⟩
  smul := fun a w => by rw [j.map_smul, hp.smul]

end AlgebraicPullback

section LocalSetup

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- All geometric inputs, including the actual complex hyperplane bundle,
follow from the original functional hypotheses on an arbitrary local complex
subspace. No ambient norm is imposed on the algebraic original space. -/
theorem exists_complexFunctional_exactSectionSetup {n : ℕ} {p : X → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) (hSphere : ComplexSphereLipschitz n p)
    (hSections : RealEquivalentSections n p)
    (Y : Submodule ℂ X) (hY : Module.rank ℂ Y = ((n + 1 : ℕ) : Cardinal))
    (μ : Measure (EuclideanSpace ℝ (Fin (2 * n)))) [μ.IsAddHaarMeasure] :
    ∃ f : ComplexHermitianAmbient n ≃ₗ[ℂ] Y, ∃ L : ℝ≥0,
      LipschitzWith L (fun v => p (f v : X)) ∧
      IsDefiniteComplexHomogeneous (fun v => p (f v : X)) ∧
      RealEquivalentSections n (fun v => p (f v : X)) ∧
      ∀ u₀ : Metric.sphere (0 : ComplexHermitianAmbient n) 1,
        Nonempty (ExactSectionPrincipalData (2 * n) (fun v => p (f v : X))
          (complexHyperplaneField n) u₀) := by
  obtain ⟨f, L, hL⟩ := exists_complex_regular_coordinates hp hSphere Y hY
  let j : ComplexHermitianAmbient n →ₗ[ℂ] X := Y.subtype.comp f.toLinearMap
  have hj : Function.Injective j := Subtype.val_injective.comp f.injective
  have hpj := hp.pullback j hj
  have hSj := hSections.pullback j hj
  refine ⟨f, L, hL, hpj, hSj, ?_⟩
  intro u₀
  exact nonempty_complexFunctional_exactSectionPrincipalData μ hpj hL.lipschitzOnWith hSj u₀

end LocalSetup

/-- The polynomial argument can work in ordinary real Euclidean coordinates;
its actual quadratic conclusion transports isometrically back to the original
complex module and reconstructs the desired Hermitian square there. -/
theorem hasHermitianSquare_of_realCoordinateQuadratic {n : ℕ}
    {p : ComplexHermitianAmbient n → ℝ} (hp : IsDefiniteComplexHomogeneous p)
    (q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin (2 * (n + 1)))))
    (hq : ∀ x, q x = p (complexHermitianAmbient_realCoordinates n x) ^ 2) :
    HasHermitianSquare p := by
  let e := complexHermitianAmbient_realCoordinates n
  apply hasHermitianSquare_of_realQuadratic hp (q.comp e.symm.toLinearEquiv.toLinearMap)
  intro v
  change q (e.symm v) = p v ^ 2
  rw [hq]
  exact congrArg (fun w => p w ^ 2) (e.apply_symm_apply v)

end

end BanachIsometric
