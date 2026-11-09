import BanachIsometric.RealMetricGaugeCollapse

/-! The remaining real metric reconstruction. The positive bilinear
representations of the actual proper ball gauges are explicit rigidity inputs;
this file does not claim the real Banach theorem. Collapse, compatibility,
completeness and the radial original-metric formula are proved internally. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem exists_real_hilbert_metric_model_of_ball_gauges [CompleteSpace X]
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X)) (Radii : Set ℝ)
    (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hconv : ∀ r ∈ Radii, Convex ℝ (Metric.closedBall (0 : X) r))
    (hforms : ∀ r ∈ Radii, Metric.closedBall (0 : X) r ≠ univ →
      Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r))) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      CompleteSpace (GaugeNormModel D) ∧ Nonempty (X ≃L[ℝ] GaugeNormModel D) := by
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  let S : Set ℝ := {r | r ∈ Radii ∧ r < dist x₀ 0}
  have hS : CofinalPositiveRadii S := cofinalPositiveRadii_restrict
    (cofinalPositiveRadii_of_zero_mem_closure hRpos hRzero) (dist_pos.mpr hx₀)
  obtain ⟨r₀, hr₀, _, _⟩ := hS 1 zero_lt_one
  obtain ⟨D⟩ := hforms r₀ hr₀.1 (centeredBall_proper_of_lt_distance x₀ hr₀.2)
  have hscale : ∀ r ∈ S, ∃ c : ℝ, 0 < c ∧
      ∀ x : X, centeredBallGauge r x = c * centeredBallGauge r₀ x := by
    intro r hr
    obtain ⟨Q⟩ := hforms r hr.1 (centeredBall_proper_of_lt_distance x₀ hr.2)
    exact real_centeredBallGauge_proportional hn hdim hmetric r₀ r D Q
  exact ⟨r₀, hr₀.1, D,
    completeSpace_gaugeNormModel_of_ball_gauges D hTI S hS (fun r hr => hconv r hr.1) hscale,
    ⟨gaugeContinuousLinearEquivOfBallGauges D hTI S hS (fun r hr => hconv r hr.1) hscale⟩⟩

theorem exists_real_radial_metric_profile_of_convex_balls
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℝ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hconv : ∀ r : ℝ, 0 < r → Convex ℝ (Metric.closedBall (0 : X) r))
    (hforms : ∀ r : ℝ, 0 < r → Metric.closedBall (0 : X) r ≠ univ →
      Nonempty (PositiveGaugeData (centeredBallGauge (X := X) r))) :
    ∃ r₀ : ℝ, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
        (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
        ∀ x y : X, dist x y = φ ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ := by
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  letI : Nontrivial X := ⟨⟨x₀, 0, hx₀⟩⟩
  let r₀ : ℝ := dist x₀ 0 / 2
  have hr₀ : 0 < r₀ := half_pos (dist_pos.mpr hx₀)
  obtain ⟨D⟩ := hforms r₀ hr₀ (centeredBall_proper_of_lt_distance x₀ (half_lt_self (dist_pos.mpr hx₀)))
  refine ⟨r₀, D, ?_⟩
  apply exists_radial_metric_profile_of_proportional_ball_gauges D hTI hconv
  exact real_proper_ball_gauges_proportional hn hdim hmetric r₀ D hforms

end
end BanachIsometric.MetricGeometry
