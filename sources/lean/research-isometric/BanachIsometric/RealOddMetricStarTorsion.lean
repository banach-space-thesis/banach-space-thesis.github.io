import BanachIsometric.RealOddFunctionalTorsion
import BanachIsometric.RadialBallFunctionalRegularity
import BanachIsometric.QuaternionicMetricStarBodyReduction
import BanachIsometric.RealMetricReconstruction
import BanachIsometric.MetricGaugeCarrier
import BanachIsometric.MetricGroupUniformity

/-! The real ODD-section metric star-body branch. Positive bilinear gauges
are derived from the actual finite radial ball descriptions and the original
metric isometries. No convexity, initial quadraticity, even-section Banach
result or replacement metric is assumed. -/

namespace BanachIsometric.MetricGeometry

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]

theorem real_ballGauge_realEquivalentSections {n : ℕ}
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n) (r : ℝ) :
    RealEquivalentRealSections n (centeredBallGauge (X := X) r) := by
  intro E F hE hF
  obtain ⟨T, hT⟩ := hmetric E F hE hF
  exact ⟨T, fun x => centeredBallGauge_preserved_scalar_subspace T hT r x⟩

theorem real_ballGauge_localSphereLipschitz_of_radial_sections {n : ℕ} {r : ℝ}
    (hsections : FiniteScalarRadialBallSections (R := ℝ) (X := X) r) :
    RealLocalSphereLipschitz n (centeredBallGauge (X := X) r) := by
  intro Y hfinite hY
  letI : FiniteDimensional ℝ Y := hfinite
  have hYbot : Y ≠ ⊥ := by intro hz; rw [hz, finrank_bot] at hY; omega
  obtain ⟨d, ⟨D⟩⟩ := hsections Y hfinite hYbot
  let e := LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin (n + 1))) Y (by rw [hY]; simp)
  let er := e.trans (Y.restrictScalarsEquiv ℝ).symm
  obtain ⟨L, hL⟩ := D.exists_gauge_lipschitz_in_coordinates er
  exact ⟨e, L, hL.lipschitzOnWith⟩

variable (hTorsion : ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin d)) ∈ interior S →
  ∀ j : ℕ, Even (j + 2) →
  ∀ α : HomotopyGroup (Fin (j + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

theorem real_odd_ballGauge_positiveGaugeData_of_radial_sections
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    {r : ℝ} (hr : 0 < r) (hsections : FiniteScalarRadialBallSections (R := ℝ) (X := X) r) :
    Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r)) := by
  have hp := (finiteScalarRadialBallSections_gauge_data (R := ℝ) hr hsections).1
  exact positiveGaugeData_of_real_odd_sections_of_body_even_homotopy_torsion hTorsion hp
    hn hodd hdim (real_ballGauge_localSphereLipschitz_of_radial_sections hsections)
    (real_ballGauge_realEquivalentSections hmetric r)

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem real_odd_hilbert_metric_model_of_radial_balls_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hcomplete : @CompleteSpace X (IsTopologicalAddGroup.toUniformSpace X))
    (Radii : Set ℝ) (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hsections : ∀ r ∈ Radii, FiniteScalarRadialBallSections (R := ℝ) (X := X) r) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      CompleteSpace (GaugeNormModel D) ∧ ∃ e : X ≃L[ℝ] GaugeNormModel D,
        ∀ x, ‖e x‖ = centeredBallGauge r₀ x := by
  letI : CompleteSpace X := (completeSpace_metric_iff_canonical hTI).mpr hcomplete
  have hR := cofinalPositiveRadii_of_zero_mem_closure hRpos hRzero
  have hforms (r : ℝ) (hr : r ∈ Radii) : Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r)) :=
    real_odd_ballGauge_positiveGaugeData_of_radial_sections hTorsion hn hodd hdim hmetric (hRpos hr) (hsections r hr)
  obtain ⟨r₀, hr₀, _, _⟩ := hR 1 zero_lt_one
  obtain ⟨D⟩ := hforms r₀ hr₀
  have hconv : ∀ r ∈ Radii, Convex ℝ (closedBall (0 : X) r) := by
    intro r hr
    obtain ⟨Q⟩ := hforms r hr
    exact convex_centeredBall_of_positive_gauge_data Q r
      (finiteScalarRadialBallSections_gauge_data (R := ℝ) (hRpos hr) (hsections r hr)).2
  have hscale : ∀ r ∈ Radii, ∃ c : ℝ, 0 < c ∧
      ∀ x : X, centeredBallGauge r x = c * centeredBallGauge r₀ x := by
    intro r hr
    obtain ⟨Q⟩ := hforms r hr
    exact real_centeredBallGauge_proportional (by omega) hdim hmetric r₀ r D Q
  refine ⟨r₀, hr₀, D,
    completeSpace_gaugeNormModel_of_ball_gauges D hTI Radii hR hconv hscale,
    gaugeContinuousLinearEquivOfBallGauges D hTI Radii hR hconv hscale, ?_⟩
  intro x
  exact norm_gaugeNormModel D (toGaugeNormModel D x)

end
end BanachIsometric.MetricGeometry
