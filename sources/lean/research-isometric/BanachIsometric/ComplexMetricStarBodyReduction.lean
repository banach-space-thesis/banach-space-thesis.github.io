import BanachIsometric.QuaternionicMetricStarBodyReduction

/-! Complex counterpart of the actual radial metric-ball to functional-A
reduction. The sphere coordinates retain precisely the paper's arbitrary
real auxiliary interpretation, and A remains an explicit rigidity premise. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped NNReal

noncomputable section

attribute [local instance] RestrictScalars.moduleOrig

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]
    [MetricSpace X]

def complexRealSubmoduleCanonicalEquiv (Y : Submodule ℂ X) :
    Y.restrictScalars ℝ ≃ₗ[ℝ] RestrictScalars ℝ ℂ Y :=
  { AddEquiv.refl Y with
    map_smul' := by
      intro r x
      apply Subtype.ext
      change r • (x : X) = (algebraMap ℝ ℂ r) • (x : X)
      exact (algebraMap_smul ℂ r (x : X)).symm }

theorem complex_sphereLipschitz_of_radial_ball_sections {n : ℕ} {r : ℝ}
    (hsections : ∀ Y : Submodule ℂ X, Module.rank ℂ Y = ((n + 1 : ℕ) : Cardinal) →
      ∃ d : ℕ, Nonempty (RadialBallSection r (Y.restrictScalars ℝ) d)) :
    ComplexSphereLipschitz n (centeredBallGauge (X := X) r) := by
  intro Y hY
  obtain ⟨d, ⟨D⟩⟩ := hsections Y hY
  letI : Module.Finite ℂ Y := Module.finite_of_rank_eq_nat hY
  have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) = Module.finrank ℂ Y := by
    rw [Module.finrank_eq_of_rank_eq hY]
    simp
  let f := LinearEquiv.ofFinrankEq (EuclideanSpace ℂ (Fin (n + 1))) Y hd
  let e : RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))) ≃ₗ[ℝ]
      RestrictScalars ℝ ℂ Y :=
    { f.toAddEquiv with map_smul' := fun r x => f.map_smul (r : ℂ) x }
  letI : Module.Finite ℂ (RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :=
    inferInstanceAs (Module.Finite ℂ (EuclideanSpace ℂ (Fin (n + 1))))
  letI : Module.Finite ℝ (RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :=
    Module.Finite.trans ℂ (RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))))
  let er := e.trans (complexRealSubmoduleCanonicalEquiv Y).symm
  obtain ⟨L, hL⟩ := D.exists_gauge_lipschitz_in_coordinates er
  exact ⟨e, L, hL.lipschitzOnWith⟩

theorem complex_ballGauge_realEquivalentSections {n : ℕ}
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n) (r : ℝ) :
    RealEquivalentSections n (centeredBallGauge (X := X) r) := by
  intro Y Z hY hZ
  obtain ⟨T, hT⟩ := hmetric Y Z (Module.finrank_eq_of_rank_eq hY) (Module.finrank_eq_of_rank_eq hZ)
  refine ⟨{ T.toAddEquiv with map_real_smul := fun r x => T.map_smul (r : ℂ) x }, ?_⟩
  intro x
  exact centeredBallGauge_preserved_scalar_subspace T hT r x

theorem complex_ballGauge_hermitian_of_functionalStatement
    (hA : ComplexFunctionalStatement (X := X))
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    {r : ℝ} (hr : 0 < r)
    (hsections : FiniteScalarRadialBallSections (R := ℂ) (X := X) r)
    (hcircled : ScalarCircled (R := ℂ) (Metric.closedBall (0 : X) r)) :
    HasHermitianSquare (centeredBallGauge (X := X) r) := by
  obtain ⟨hq, _⟩ := finiteScalarRadialBallSections_gauge_data hr hsections
  have hb := finiteScalarRadialBallSections_balanced hr hsections hcircled
  have hhom : IsDefiniteComplexHomogeneous (centeredBallGauge (X := X) r) :=
    { nonneg := hq.nonneg
      eq_zero_iff := hq.eq_zero_iff
      smul := fun a x => centeredBallGauge_smul_divisionAlgebra hb a x }
  apply hA n _ hn hdim hhom
  · apply complex_sphereLipschitz_of_radial_ball_sections
    intro Y hY
    letI : Module.Finite ℂ Y := Module.finite_of_rank_eq_nat hY
    have hfin : Module.finrank ℂ Y = n + 1 := Module.finrank_eq_of_rank_eq hY
    have hYbot : Y ≠ ⊥ := by
      intro hz
      rw [hz, finrank_bot] at hfin
      omega
    exact hsections Y inferInstance hYbot
  · exact complex_ballGauge_realEquivalentSections hmetric r

end
end BanachIsometric.MetricGeometry

