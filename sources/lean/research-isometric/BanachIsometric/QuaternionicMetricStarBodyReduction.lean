import BanachIsometric.OppositeNormedDivisionRing
import BanachIsometric.RadialBallFunctionalRegularity
import BanachIsometric.CircledRadialBallGauge
import BanachIsometric.MetricGaugeIsometries

/-! The quaternionic star-body branch of the metric theorem really supplies
the functional theorem's hypotheses. The functional rigidity assertion itself
is passed explicitly, and is not asserted as an axiom or as a proved theorem. -/

namespace BanachIsometric.MetricGeometry

open Set

noncomputable section

section DivisionAlgebra

variable {R X : Type*} [NormedDivisionRing R] [NormedAlgebra ℝ R]
    [AddCommGroup X] [Module R X] [Module ℝ X] [IsScalarTower ℝ R X] [MetricSpace X]

/-- Every nonzero finite scalar subspace has the actual positive Lipschitz
radial description required in the paper, in auxiliary real coordinates. -/
def FiniteScalarRadialBallSections (r : ℝ) : Prop :=
  ∀ Y : Submodule R X, FiniteDimensional R Y → Y ≠ ⊥ →
    ∃ d : ℕ, Nonempty (RadialBallSection r (Y.restrictScalars ℝ) d)

theorem finiteScalarRadialBallSections_point_section {r : ℝ}
    (h : FiniteScalarRadialBallSections (R := R) (X := X) r) (x : X) (hx : x ≠ 0) :
    ∃ P : Submodule ℝ X, ∃ _hx : x ∈ P, ∃ d : ℕ, Nonempty (RadialBallSection r P d) := by
  let Y : Submodule R X := R ∙ x
  have hY : Y ≠ ⊥ := Submodule.span_singleton_eq_bot.not.mpr hx
  obtain ⟨d, D⟩ := h Y inferInstance hY
  exact ⟨Y.restrictScalars ℝ, Submodule.mem_span_singleton_self x, d, D⟩

theorem finiteScalarRadialBallSections_gauge_data {r : ℝ} (hr : 0 < r)
    (h : FiniteScalarRadialBallSections (R := R) (X := X) r) :
    AlgebraicPositiveHomogeneous (centeredBallGauge (X := X) r) ∧
      ∀ x : X, centeredBallGauge r x ≤ 1 ↔ dist x 0 ≤ r :=
  centeredBallGauge_algebraic_of_radial_sections hr (finiteScalarRadialBallSections_point_section h)

theorem finiteScalarRadialBallSections_balanced {r : ℝ} (hr : 0 < r)
    (h : FiniteScalarRadialBallSections (R := R) (X := X) r)
    (hcircled : ScalarCircled (R := R) (Metric.closedBall (0 : X) r)) :
    Balanced R (Metric.closedBall (0 : X) r) := by
  obtain ⟨hq, hcarrier⟩ := finiteScalarRadialBallSections_gauge_data hr h
  exact balanced_centeredBall_of_circled_radial_gauge hcircled hq hcarrier

end DivisionAlgebra

section Quaternionic

open Quaternionic
attribute [local instance] RestrictScalars.moduleOrig

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [IsScalarTower ℝ Hᵐᵒᵖ X] [MetricSpace X]

theorem quaternionic_ballGauge_realEquivalentSections {n : ℕ}
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n) (r : ℝ) :
    Quaternionic.RealEquivalentSections n (centeredBallGauge (X := X) r) := by
  intro Y Z hY hZ
  obtain ⟨T, hT⟩ := hmetric Y Z (Module.finrank_eq_of_rank_eq hY) (Module.finrank_eq_of_rank_eq hZ)
  refine ⟨canonicalRealEquiv T, ?_⟩
  intro x
  exact centeredBallGauge_preserved_scalar_subspace T hT r x

theorem quaternionic_ballGauge_hermitian_of_functionalStatement
    (hA : Quaternionic.FunctionalStatement (E := X))
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := Hᵐᵒᵖ) (X := X) n)
    {r : ℝ} (hr : 0 < r)
    (hsections : FiniteScalarRadialBallSections (R := Hᵐᵒᵖ) (X := X) r)
    (hcircled : ScalarCircled (R := Hᵐᵒᵖ) (Metric.closedBall (0 : X) r)) :
    Quaternionic.HasHermitianSquare (centeredBallGauge (X := X) r) := by
  obtain ⟨hq, _⟩ := finiteScalarRadialBallSections_gauge_data hr hsections
  have hb := finiteScalarRadialBallSections_balanced hr hsections hcircled
  have hhom : Quaternionic.IsDefiniteHomogeneous (centeredBallGauge (X := X) r) :=
    { nonneg := hq.nonneg
      eq_zero_iff := hq.eq_zero_iff
      right_mul := fun x a => by
        change centeredBallGauge r (MulOpposite.op a • x) = centeredBallGauge r x * ‖a‖
        rw [centeredBallGauge_smul_divisionAlgebra hb]
        exact mul_comm _ _ }
  apply hA n _ hn hdim hhom
  · apply quaternionic_sphereLipschitz_of_radial_ball_sections
    intro Y hY
    letI : Module.Finite Hᵐᵒᵖ Y := Module.finite_of_rank_eq_nat hY
    have hfin : Module.finrank Hᵐᵒᵖ Y = n + 1 := Module.finrank_eq_of_rank_eq hY
    have hYbot : Y ≠ ⊥ := by
      intro hz
      rw [hz, finrank_bot] at hfin
      omega
    exact hsections Y inferInstance hYbot
  · exact quaternionic_ballGauge_realEquivalentSections hmetric r

end Quaternionic

end
end BanachIsometric.MetricGeometry


