import BanachIsometric.MetricHermitianReconstruction

/-! Scalar-preserving topology reconstruction and the convexity recovered
from an actual Hermitian ball gauge, even in the star-body alternative. -/

namespace BanachIsometric.MetricGeometry

open Set

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]

theorem convex_centeredBall_of_positive_gauge_data {q : X → ℝ} (D : PositiveGaugeData q)
    (r : ℝ) (hcarrier : ∀ x : X, q x ≤ 1 ↔ dist x 0 ≤ r) :
    Convex ℝ (Metric.closedBall (0 : X) r) := by
  let e := toGaugeNormModel D
  have heq : Metric.closedBall (0 : X) r = e ⁻¹' Metric.closedBall 0 1 := by
    ext x
    change dist x 0 ≤ r ↔ dist (e x) 0 ≤ 1
    rw [dist_zero_right, norm_gaugeNormModel]
    exact (hcarrier x).symm
  rw [heq]
  exact (convex_closedBall (0 : GaugeNormModel D) 1).linear_preimage e.toLinearMap

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

section Scalars

variable {R : Type*} [Semiring R] [Module R X]

def gaugeContinuousLinearEquivScalarOfBallGauges {q : X → ℝ} (D : PositiveGaugeData q)
    (hTI : TranslationInvariant (X := X)) (S : Set ℝ) (hS : CofinalPositiveRadii S)
    (hconv : ∀ r ∈ S, Convex ℝ (Metric.closedBall (0 : X) r))
    (hscale : ∀ r ∈ S, ∃ c : ℝ, 0 < c ∧ ∀ x : X, centeredBallGauge r x = c * q x) :
    X ≃L[R] GaugeNormModel D :=
  { toGaugeNormModelScalar (R := R) D with
    continuous_toFun := (gaugeUniformEquivOfBallGauges D hTI S hS hconv hscale).uniformContinuous.continuous
    continuous_invFun := (gaugeUniformEquivOfBallGauges D hTI S hS hconv hscale).symm.uniformContinuous.continuous }

end Scalars

end
end BanachIsometric.MetricGeometry
