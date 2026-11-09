import BanachIsometric.MetricGaugeNormTopology
import BanachIsometric.RadialMetricRepresentation

/-! The metric part of Theorem E after the Hermitian rigidity step.
The hypotheses below specify the actual gauges of the original metric balls,
not a replacement metric. The proportionality input is explicit; topology,
completeness and the final radial profile are constructed here. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped NNReal

noncomputable section

theorem cofinalPositiveRadii_of_zero_mem_closure {R : Set ℝ}
    (hpos : R ⊆ Set.Ioi 0) (hzero : (0 : ℝ) ∈ closure R) : CofinalPositiveRadii R := by
  intro ε hε
  obtain ⟨r, hr, hdist⟩ := Metric.mem_closure_iff.mp hzero ε hε
  refine ⟨r, hr, hpos hr, ?_⟩
  simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (show 0 < r from hpos hr)] using hdist

theorem zero_mem_closure_of_cofinalPositiveRadii {R : Set ℝ} (hR : CofinalPositiveRadii R) :
    (0 : ℝ) ∈ closure R := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨r, hrR, hr, hsmall⟩ := hR ε hε
  exact ⟨r, hrR, by simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hr] using hsmall⟩

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

theorem PositiveGaugeData.algebraicPositiveHomogeneous {q : X → ℝ} (D : PositiveGaugeData q) :
    AlgebraicPositiveHomogeneous q where
  nonneg := D.nonneg
  eq_zero_iff := D.eq_zero_iff
  smul_nonneg t ht x := by
    let e := toGaugeNormModel D
    calc
      q (t • x) = ‖e (t • x)‖ := (norm_gaugeNormModel D (e (t • x))).symm
      _ = ‖t • e x‖ := congrArg norm (e.map_smul t x)
      _ = t * ‖e x‖ := by rw [norm_smul, Real.norm_of_nonneg ht]
      _ = t * q x := by rw [norm_gaugeNormModel]; rfl

variable [MetricSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Actual proper convex balls whose Minkowski functionals are proportional
have the indicated exact sublevel sets. Whole-space balls remain allowed. -/
theorem closedBallGaugeRepresentation_of_proportional_gauges {q : X → ℝ}
    (hconv : ∀ r : ℝ, 0 < r → Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r : ℝ, 0 < r → Metric.closedBall (0 : X) r ≠ univ →
      ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x) :
    ClosedBallGaugeRepresentation q := by
  intro r hr
  by_cases hwhole : Metric.closedBall (0 : X) r = univ
  · exact Or.inl hwhole
  · obtain ⟨c, hc, hcr⟩ := hscale r hr hwhole
    refine Or.inr ⟨c⁻¹, ?_⟩
    ext x
    change dist x 0 ≤ r ↔ q x ≤ c⁻¹
    rw [← centeredBallGauge_le_one_iff hr (hconv r hr), hcr]
    constructor
    · intro hx
      have h := (div_le_div_iff_of_pos_right hc).mpr hx
      simpa only [mul_div_cancel_left₀ _ hc.ne', one_div] using h
    · intro hx
      have h := mul_le_mul_of_nonneg_left hx hc.le
      simpa only [mul_inv_cancel₀ hc.ne'] using h

/-- The last assertion of Theorem E, conditional only on the stated
Hermitian/proportionality step for actual proper centered-ball gauges. -/
theorem exists_radial_metric_profile_of_proportional_ball_gauges [Nontrivial X]
    {q : X → ℝ} (D : PositiveGaugeData q) (hTI : TranslationInvariant (X := X))
    (hconv : ∀ r : ℝ, 0 < r → Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r : ℝ, 0 < r → Metric.closedBall (0 : X) r ≠ univ →
      ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x) :
    ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
      (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
      ∀ x y : X, dist x y = φ ⟨q (x - y), D.nonneg (x - y)⟩ :=
  exists_radial_metric_profile D.algebraicPositiveHomogeneous hTI
    (closedBallGaugeRepresentation_of_proportional_gauges hconv hscale)

/-- Cofinal proper radii give a complete genuine Hilbert norm model with
exactly the original uniformity. The original metric on X is unchanged. -/
theorem exists_complete_gaugeNormModel_of_proper_ball_gauges [Nontrivial X] [CompleteSpace X]
    {q : X → ℝ} (D : PositiveGaugeData q) (hTI : TranslationInvariant (X := X))
    (R : Set ℝ) (hR : CofinalPositiveRadii R)
    (hconv : ∀ r ∈ R, Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r ∈ R, Metric.closedBall (0 : X) r ≠ univ →
      ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x) :
    ∃ S : Set ℝ, S ⊆ R ∧ CofinalPositiveRadii S ∧
      Nonempty (X ≃L[ℝ] GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) := by
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
  let S : Set ℝ := {r | r ∈ R ∧ r < dist x₀ 0}
  have hSR : S ⊆ R := fun _ hr => hr.1
  have hS : CofinalPositiveRadii S := cofinalPositiveRadii_restrict hR (dist_pos.mpr hx₀)
  have hscaleS : ∀ r ∈ S, ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x := by
    intro r hr
    exact hscale r hr.1 (centeredBall_proper_of_lt_distance x₀ hr.2)
  exact ⟨S, hSR, hS, ⟨gaugeContinuousLinearEquivOfBallGauges D hTI S hS
    (fun r hr => hconv r hr.1) hscaleS⟩,
    completeSpace_gaugeNormModel_of_ball_gauges D hTI S hS (fun r hr => hconv r hr.1) hscaleS⟩

end
end BanachIsometric.MetricGeometry

