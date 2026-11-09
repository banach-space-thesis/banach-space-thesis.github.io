import BanachIsometric.QuaternionicFunctionalGeometry

/-! The original algebraic local quaternionic space obtains actual right
quaternionic Euclidean coordinates and all geometric inputs, while the
original arbitrary real-coordinate sphere regularity is retained faithfully. -/

namespace BanachIsometric.Quaternionic

open Set MeasureTheory
open scoped Quaternion NNReal

noncomputable section

attribute [local instance] RestrictScalars.moduleOrig

section Coordinates

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X]

theorem exists_regular_coordinates {p : X → ℝ} (hp : IsDefiniteHomogeneous p)
    {n : ℕ} (hSphere : SphereLipschitz n p)
    (Y : Submodule Hᵐᵒᵖ X) (hY : Module.rank Hᵐᵒᵖ Y = ((n + 1 : ℕ) : Cardinal)) :
    ∃ f : HermitianAmbient n ≃ₗ[Hᵐᵒᵖ] Y, ∃ L : ℝ≥0,
      LipschitzWith L (fun v => p (f v : X)) := by
  obtain ⟨e, C, hC⟩ := hSphere Y hY
  have hpY := hp.pullback Y.subtype Subtype.val_injective
  have hpE := hpY.restrictReal.pullback e.toLinearMap e.injective
  obtain ⟨L, hL⟩ := hpE.exists_lipschitzWith hC
  letI : Module.Finite Hᵐᵒᵖ Y := Module.finite_of_rank_eq_nat hY
  have hdim : Module.finrank Hᵐᵒᵖ (HermitianAmbient n) = Module.finrank Hᵐᵒᵖ Y := by
    rw [finrank_right_euclidean, Module.finrank_eq_of_rank_eq hY]
  let f := LinearEquiv.ofFinrankEq (HermitianAmbient n) Y hdim
  let fr := domainRealEquiv f
  let T : HermitianAmbient n →L[ℝ] EuclideanSpace ℝ (Fin (4 * (n + 1))) :=
    (e.symm.toLinearMap.comp fr.toLinearMap).toContinuousLinearMap
  refine ⟨f, L * ‖T‖₊, ?_⟩
  simpa [T, fr, domainRealEquiv, Function.comp_def, RestrictScalars.addEquiv] using hL.comp T.lipschitz

/-- Every local right-quaternionic `(n+1)`-space in the original functional
hypotheses yields the actual auxiliary hyperplane principal bundle. -/
theorem exists_functional_exactSectionSetup {n : ℕ} {p : X → ℝ}
    (hp : IsDefiniteHomogeneous p) (hSphere : SphereLipschitz n p)
    (hSections : RealEquivalentSections n p)
    (Y : Submodule Hᵐᵒᵖ X) (hY : Module.rank Hᵐᵒᵖ Y = ((n + 1 : ℕ) : Cardinal))
    (μ : Measure (EuclideanSpace ℝ (Fin (4 * n)))) [μ.IsAddHaarMeasure] :
    ∃ f : HermitianAmbient n ≃ₗ[Hᵐᵒᵖ] Y, ∃ L : ℝ≥0,
      LipschitzWith L (fun v => p (f v : X)) ∧
      IsDefiniteHomogeneous (fun v => p (f v : X)) ∧
      RealEquivalentSections n (fun v => p (f v : X)) ∧
      ∀ u₀ : Metric.sphere (0 : HermitianAmbient n) 1,
        Nonempty (ExactSectionPrincipalData (4 * n) (fun v => p (f v : X)) (hyperplaneField n) u₀) := by
  obtain ⟨f, L, hL⟩ := exists_regular_coordinates hp hSphere Y hY
  let j : HermitianAmbient n →ₗ[Hᵐᵒᵖ] X := Y.subtype.comp f.toLinearMap
  have hj : Function.Injective j := Subtype.val_injective.comp f.injective
  have hpj := hp.pullback j hj
  have hSj := hSections.pullback j hj
  exact ⟨f, L, hL, hpj, hSj, fun u₀ =>
    nonempty_functional_exactSectionPrincipalData μ hpj hL.lipschitzOnWith hSj u₀⟩

end Coordinates

/-- A real quadratic conclusion in honest real Euclidean coordinates
reconstructs a positive Hermitian square for the original right action. -/
theorem hasHermitianSquare_of_realCoordinateQuadratic {n : ℕ}
    {p : HermitianAmbient n → ℝ} (hp : IsDefiniteHomogeneous p)
    (q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin (4 * (n + 1)))))
    (hq : ∀ x, q x = p ((realCoordinateIsometry (n + 1)).symm x) ^ 2) :
    HasHermitianSquare p := by
  let e := realCoordinateIsometry (n + 1)
  apply hasHermitianSquare_of_realQuadratic hp (q.comp e.toLinearEquiv.toLinearMap)
  intro v
  change q (e v) = p v ^ 2
  rw [hq, e.symm_apply_apply]

end
end BanachIsometric.Quaternionic
