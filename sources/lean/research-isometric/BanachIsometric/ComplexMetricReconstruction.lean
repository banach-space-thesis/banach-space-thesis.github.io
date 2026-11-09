import BanachIsometric.ScalarMetricGaugeCollapse
import BanachIsometric.MetricGaugeCarrier

/-! Complete scalar-preserving metric reconstruction from actual Hermitian
ball gauges. Their proportionality is proved from the actual linear metric
hypothesis; neither collapse nor topology agreement is an input. -/

namespace BanachIsometric.MetricGeometry

open Set

noncomputable section



variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X]
    [IsScalarTower ℝ ℂ X] [MetricSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [CompleteSpace X]

theorem exists_complex_hilbert_metric_model_of_ball_gauges
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X)) (Radii : Set ℝ) (hR : CofinalPositiveRadii Radii)
    (hbal : ∀ r ∈ Radii, Balanced ℂ (Metric.closedBall (0 : X) r))
    (hcarrier : ∀ r ∈ Radii, ∀ x : X, centeredBallGauge r x ≤ 1 ↔ dist x 0 ≤ r)
    (hforms : ∀ r ∈ Radii, HasHermitianSquare (centeredBallGauge (X := X) r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass ℂ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      Nonempty (X ≃L[ℂ] GaugeNormModel D) := by
  obtain ⟨r₀, hr₀, _, _⟩ := hR 1 zero_lt_one
  have hp := hforms r₀ hr₀
  obtain ⟨pForm, hpForm⟩ := hp
  let D := complexPositiveGaugeData pForm hpForm (fun x => gauge_nonneg x)
  have hconv : ∀ r ∈ Radii, Convex ℝ (Metric.closedBall (0 : X) r) := by
    intro r hr
    obtain ⟨qForm, hqForm⟩ := hforms r hr
    exact convex_centeredBall_of_positive_gauge_data
      (complexPositiveGaugeData qForm hqForm (fun x => gauge_nonneg x)) r (hcarrier r hr)
  have hscale : ∀ r ∈ Radii, ∃ c : ℝ, 0 < c ∧
      ∀ x : X, centeredBallGauge r x = c * centeredBallGauge r₀ x := by
    intro r hr
    exact complex_centeredBallGauge_proportional hn hdim hmetric r₀ r (hbal r₀ hr₀) ⟨pForm, hpForm⟩ (hforms r hr)
  have hnormsmul : NormSMulClass ℂ (GaugeNormModel D) :=
    gaugeNormModelNormSMul (R := ℂ) (X := X) D
      (fun a x => centeredBallGauge_smul_divisionAlgebra (R := ℂ) (X := X) (hbal r₀ hr₀) a x)
  have hpM : HasHermitianSquare (norm : GaugeNormModel D → ℝ) := by
    refine ⟨pForm, ?_⟩
    intro x
    change pForm.form x x = ((‖x‖ ^ 2 : ℝ) : ℂ)
    rw [norm_gaugeNormModel]
    exact hpForm x
  exact ⟨r₀, hr₀, D, hnormsmul,
    completeSpace_gaugeNormModel_of_ball_gauges D hTI Radii hR hconv hscale,
    hpM, ⟨gaugeContinuousLinearEquivScalarOfBallGauges D hTI Radii hR hconv hscale⟩⟩

end
end BanachIsometric.MetricGeometry


