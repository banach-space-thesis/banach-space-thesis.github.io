import BanachIsometric.RealEvenFunctionalRigidity
import BanachIsometric.RealOddMetricStarTorsion

/-! The actual real even-section metric star-body branch. Positive bilinear
ball gauges are derived, and the original metric topology and completeness
are retained. No initial quadraticity or external topological premise occurs. -/

namespace BanachIsometric.MetricGeometry

open Set Metric MeasureTheory
open scoped Topology NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]
theorem real_even_ballGauge_positiveGaugeData_of_radial_sections
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    {r : ℝ} (hr : 0 < r) (hsections : FiniteScalarRadialBallSections (R := ℝ) (X := X) r) :
    Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r)) := by
  have hp := (finiteScalarRadialBallSections_gauge_data (R := ℝ) hr hsections).1
  exact positiveGaugeData_of_real_even_sections hp
    hn heven hdim (real_ballGauge_localSphereLipschitz_of_radial_sections hsections)
    (real_ballGauge_realEquivalentSections hmetric r)

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem real_even_hilbert_metric_model_of_radial_balls
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ X)
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
    real_even_ballGauge_positiveGaugeData_of_radial_sections hn heven hdim hmetric (hRpos hr) (hsections r hr)
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
