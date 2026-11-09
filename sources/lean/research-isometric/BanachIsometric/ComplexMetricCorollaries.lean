import BanachIsometric.ComplexMetricReconstruction
import BanachIsometric.ComplexMetricStarBodyReduction
import BanachIsometric.ConvexMetricBallRigidity
import BanachIsometric.FiniteCircledSections

/-! The metric conclusions of Theorem E for the original right complex
space, conditional on the explicitly stated functional theorem A. Both
geometric alternatives supply actual ball gauges internally. The original
distance, topology, and right action are retained throughout. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X]
    [IsScalarTower ℝ ℂ X] [MetricSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X]

/-- Cofinal absolutely convex balls, with the original scalar-linear metric
hypothesis, yield a complete compatible Hermitian norm. A is explicit. -/
theorem exists_complex_hilbert_metric_model_of_convex_balls [CompleteSpace X]
    (hA : ComplexFunctionalStatement (X := X))
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X)) (Radii : Set ℝ)
    (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hballs : ∀ r ∈ Radii, Balanced ℂ (Metric.closedBall (0 : X) r) ∧
      Convex ℝ (Metric.closedBall (0 : X) r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass ℂ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      Nonempty (X ≃L[ℂ] GaugeNormModel D) := by
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  let S : Set ℝ := {r | r ∈ Radii ∧ r < dist x₀ 0}
  have hSR : S ⊆ Radii := fun _ hr => hr.1
  have hS : CofinalPositiveRadii S := cofinalPositiveRadii_restrict
    (cofinalPositiveRadii_of_zero_mem_closure hRpos hRzero) (dist_pos.mpr hx₀)
  obtain ⟨r₀, hr₀, D, hD⟩ := exists_complex_hilbert_metric_model_of_ball_gauges hn hdim
    hmetric hTI S hS (fun r hr => (hballs r hr.1).1)
    (fun r hr x => centeredBallGauge_le_one_iff (hRpos hr.1) (hballs r hr.1).2 x)
    (fun r hr => complex_convexBallGauge_hermitian_of_functionalStatement hA hn hdim hmetric
      (hRpos hr.1) (hballs r hr.1).1 (hballs r hr.1).2 (centeredBall_proper_of_lt_distance x₀ hr.2))
  exact ⟨r₀, hSR hr₀, D, hD⟩

/-- The finite-section circled Lipschitz star-body alternative has the same
complete metric conclusion, without a convexity assumption on the balls. -/
theorem exists_complex_hilbert_metric_model_of_radial_balls [CompleteSpace X]
    (hA : ComplexFunctionalStatement (X := X))
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X)) (Radii : Set ℝ)
    (hRpos : Radii ⊆ Ioi 0) (hRzero : (0 : ℝ) ∈ closure Radii)
    (hsections : ∀ r ∈ Radii, FiniteScalarRadialBallSections (R := ℂ) (X := X) r)
    (hcircled : ∀ r ∈ Radii, ∀ Y : Submodule ℂ X, FiniteDimensional ℂ Y → Y ≠ ⊥ →
      ScalarCircled (R := ℂ) (Y.subtype ⁻¹' Metric.closedBall 0 r)) :
    ∃ r₀ ∈ Radii, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      NormSMulClass ℂ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      Nonempty (X ≃L[ℂ] GaugeNormModel D) := by
  have hCircle : ∀ r ∈ Radii, ScalarCircled (R := ℂ) (Metric.closedBall (0 : X) r) :=
    fun r hr => scalarCircled_of_finiteScalarSections (hcircled r hr)
  exact exists_complex_hilbert_metric_model_of_ball_gauges hn hdim hmetric hTI Radii
    (cofinalPositiveRadii_of_zero_mem_closure hRpos hRzero)
    (fun r hr => finiteScalarRadialBallSections_balanced (hRpos hr) (hsections r hr) (hCircle r hr))
    (fun r hr => (finiteScalarRadialBallSections_gauge_data (hRpos hr) (hsections r hr)).2)
    (fun r hr => complex_ballGauge_hermitian_of_functionalStatement hA hn hdim hmetric
      (hRpos hr) (hsections r hr) (hCircle r hr))

/-- The chosen original metric itself is radial if all its centered closed
balls are absolutely convex. Whole-space balls of bounded metrics are allowed. -/
theorem exists_complex_radial_metric_profile_of_convex_balls
    (hA : ComplexFunctionalStatement (X := X))
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hmetric : LinearMetricSubspaceHomogeneity (R := ℂ) (X := X) n)
    (hTI : TranslationInvariant (X := X))
    (hballs : ∀ r : ℝ, 0 < r → Balanced ℂ (Metric.closedBall (0 : X) r) ∧
      Convex ℝ (Metric.closedBall (0 : X) r)) :
    ∃ r₀ : ℝ, ∃ D : PositiveGaugeData (centeredBallGauge (X := X) r₀),
      ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
        (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
        ∀ x y : X, dist x y = φ ⟨centeredBallGauge r₀ (x - y), D.nonneg (x - y)⟩ := by
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  letI : Nontrivial X := ⟨⟨x₀, 0, hx₀⟩⟩
  let r₀ : ℝ := dist x₀ 0 / 2
  have hr₀ : 0 < r₀ := half_pos (dist_pos.mpr hx₀)
  have hproper : Metric.closedBall (0 : X) r₀ ≠ univ :=
    centeredBall_proper_of_lt_distance x₀ (half_lt_self (dist_pos.mpr hx₀))
  obtain ⟨pForm, hpForm⟩ := complex_convexBallGauge_hermitian_of_functionalStatement
    hA hn hdim hmetric hr₀ (hballs r₀ hr₀).1 (hballs r₀ hr₀).2 hproper
  let D := complexPositiveGaugeData pForm hpForm (fun x => gauge_nonneg x)
  refine ⟨r₀, D, ?_⟩
  apply exists_radial_metric_profile_of_proportional_ball_gauges D hTI (fun r hr => (hballs r hr).2)
  intro r hr hproperr
  exact complex_centeredBallGauge_proportional hn hdim hmetric r₀ r (hballs r₀ hr₀).1
    ⟨pForm, hpForm⟩
    (complex_convexBallGauge_hermitian_of_functionalStatement hA hn hdim hmetric hr
      (hballs r hr).1 (hballs r hr).2 hproperr)

end
end BanachIsometric.MetricGeometry

