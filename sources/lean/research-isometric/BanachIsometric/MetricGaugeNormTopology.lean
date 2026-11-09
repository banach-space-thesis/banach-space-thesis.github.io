import BanachIsometric.MetricBallGauge
import BanachIsometric.GaugeNormModel
import Mathlib.Topology.UniformSpace.Equiv

/-! Cofinal actual metric-ball gauges proportional to a Hermitian gauge
induce exactly its norm uniformity. The original metric remains on X; the
genuine inner-product norm is confined to GaugeNormModel. -/

namespace BanachIsometric.MetricGeometry

open Set Filter
open scoped Topology

noncomputable section

def CofinalPositiveRadii (R : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r ∈ R, 0 < r ∧ r < ε

theorem cofinalPositiveRadii_restrict {R : Set ℝ} (hR : CofinalPositiveRadii R)
    {a : ℝ} (ha : 0 < a) : CofinalPositiveRadii {r | r ∈ R ∧ r < a} := by
  intro ε hε
  obtain ⟨r, hrR, hr, hsmall⟩ := hR (min ε a) (lt_min hε ha)
  exact ⟨r, ⟨hrR, hsmall.trans_le (min_le_right _ _)⟩, hr,
    hsmall.trans_le (min_le_left _ _)⟩

theorem centeredBall_proper_of_lt_distance {X : Type*} [AddCommGroup X] [MetricSpace X]
    (x : X) {r : ℝ} (hr : r < dist x 0) : Metric.closedBall (0 : X) r ≠ univ := by
  intro hwhole
  have hx : x ∈ Metric.closedBall (0 : X) r := hwhole.ge (mem_univ x)
  exact hr.not_ge hx

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]

omit [MetricSpace X] in
theorem dist_toGaugeNormModel {q : X → ℝ} (D : PositiveGaugeData q) (x y : X) :
    dist (toGaugeNormModel D x) (toGaugeNormModel D y) = q (x - y) := by
  calc
    _ = ‖toGaugeNormModel D x - toGaugeNormModel D y‖ := dist_eq_norm _ _
    _ = ‖toGaugeNormModel D (x - y)‖ := congrArg norm ((toGaugeNormModel D).map_sub x y).symm
    _ = q (x - y) := norm_gaugeNormModel D (toGaugeNormModel D (x - y))

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem continuous_gauge_of_proportional_ball {q : X → ℝ} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hconv : Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ x, centeredBallGauge r x = c * q x) : Continuous q := by
  have heq : (fun x => c⁻¹ * centeredBallGauge r x) = q := by
    funext x
    rw [hscale, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  rw [← heq]
  exact continuous_const.mul (continuous_centeredBallGauge hr hconv)

omit [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] in
theorem uniformContinuous_toGaugeNormModel {q : X → ℝ} (D : PositiveGaugeData q)
    (hTI : TranslationInvariant (X := X)) (hq : Continuous q) :
    UniformContinuous (toGaugeNormModel D) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp (hq.continuousAt (x := 0)) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  rw [dist_toGaugeNormModel]
  have hz : dist (x - y) 0 < δ := by rwa [← dist_eq_dist_sub_zero hTI]
  have h := hsmall hz
  have hq0 : q 0 = 0 := (D.eq_zero_iff 0).mpr rfl
  simpa only [hq0, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (D.nonneg (x - y))] using h

theorem uniformContinuous_fromGaugeNormModel {q : X → ℝ} (D : PositiveGaugeData q)
    (hTI : TranslationInvariant (X := X)) (R : Set ℝ) (hR : CofinalPositiveRadii R)
    (hconv : ∀ r ∈ R, Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r ∈ R, ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x) :
    UniformContinuous (toGaugeNormModel D).symm := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨r, hrR, hr, hrε⟩ := hR ε hε
  obtain ⟨c, hc, hcr⟩ := hscale r hrR
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro x y hxy
  let e := toGaugeNormModel D
  have hq : q (e.symm x - e.symm y) < c⁻¹ := by
    rw [← dist_toGaugeNormModel D]
    simpa only [e.apply_symm_apply] using hxy
  have hcq : c * q (e.symm x - e.symm y) ≤ 1 := by
    have h := mul_lt_mul_of_pos_left hq hc
    rw [mul_inv_cancel₀ hc.ne'] at h
    exact h.le
  have hGauge : centeredBallGauge r (e.symm x - e.symm y) ≤ 1 := by rw [hcr]; exact hcq
  rw [dist_eq_dist_sub_zero hTI]
  exact ((centeredBallGauge_le_one_iff hr (hconv r hrR) _).mp hGauge).trans_lt hrε

theorem continuous_gauge_of_cofinal_ball_gauges {q : X → ℝ}
    (R : Set ℝ) (hR : CofinalPositiveRadii R)
    (hconv : ∀ r ∈ R, Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r ∈ R, ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x) :
    Continuous q := by
  obtain ⟨r, hrR, hr, _⟩ := hR 1 zero_lt_one
  obtain ⟨c, hc, hcr⟩ := hscale r hrR
  exact continuous_gauge_of_proportional_ball hr hc (hconv r hrR) hcr

def gaugeUniformEquivOfBallGauges {q : X → ℝ} (D : PositiveGaugeData q)
    (hTI : TranslationInvariant (X := X)) (R : Set ℝ) (hR : CofinalPositiveRadii R)
    (hconv : ∀ r ∈ R, Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r ∈ R, ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x) :
    X ≃ᵤ GaugeNormModel D :=
  { (toGaugeNormModel D).toEquiv with
    uniformContinuous_toFun := uniformContinuous_toGaugeNormModel D hTI
      (continuous_gauge_of_cofinal_ball_gauges R hR hconv hscale)
    uniformContinuous_invFun := uniformContinuous_fromGaugeNormModel D hTI R hR hconv hscale }
def gaugeContinuousLinearEquivOfBallGauges {q : X → ℝ} (D : PositiveGaugeData q)
    (hTI : TranslationInvariant (X := X)) (R : Set ℝ) (hR : CofinalPositiveRadii R)
    (hconv : ∀ r ∈ R, Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r ∈ R, ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x) :
    X ≃L[ℝ] GaugeNormModel D :=
  { toGaugeNormModel D with
    continuous_toFun := (gaugeUniformEquivOfBallGauges D hTI R hR hconv hscale).uniformContinuous.continuous
    continuous_invFun := (gaugeUniformEquivOfBallGauges D hTI R hR hconv hscale).symm.uniformContinuous.continuous }

theorem completeSpace_gaugeNormModel_of_ball_gauges [CompleteSpace X]
    {q : X → ℝ} (D : PositiveGaugeData q)
    (hTI : TranslationInvariant (X := X)) (R : Set ℝ) (hR : CofinalPositiveRadii R)
    (hconv : ∀ r ∈ R, Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r ∈ R, ∃ c : ℝ, 0 < c ∧ ∀ x, centeredBallGauge r x = c * q x) :
    CompleteSpace (GaugeNormModel D) :=
  (gaugeUniformEquivOfBallGauges D hTI R hR hconv hscale).completeSpace_iff.mp inferInstance

end
end BanachIsometric.MetricGeometry

