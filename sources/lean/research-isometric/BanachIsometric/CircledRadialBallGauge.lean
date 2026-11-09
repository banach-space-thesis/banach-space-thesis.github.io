import BanachIsometric.DivisionAlgebraGauge
import BanachIsometric.MetricStarBodyGauges

/-! The circled radial hypothesis yields balancedness over the original
possibly noncommutative scalar algebra. This is the geometric input needed
for absolute scalar homogeneity of the metric-ball Minkowski functional. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped Pointwise

noncomputable section

variable {R X : Type*} [NormedDivisionRing R] [NormedAlgebra ℝ R]
    [AddCommGroup X] [Module R X] [Module ℝ X] [IsScalarTower ℝ R X]
    [MetricSpace X]

/-- Circled means invariance under every scalar of norm one, with the given
original scalar action. It imposes no convexity. -/
def ScalarCircled (s : Set X) : Prop := ∀ a : R, ‖a‖ = 1 → a • s = s

theorem balanced_centeredBall_of_circled_radial_gauge {r : ℝ}
    (hcircled : ScalarCircled (R := R) (Metric.closedBall (0 : X) r))
    (hq : AlgebraicPositiveHomogeneous (centeredBallGauge (X := X) r))
    (hcarrier : ∀ x : X, centeredBallGauge r x ≤ 1 ↔ dist x 0 ≤ r) :
    Balanced R (Metric.closedBall (0 : X) r) := by
  apply balanced_iff_smul_mem.mpr
  intro a ha x hx
  by_cases ha₀ : a = 0
  · rw [ha₀, zero_smul]
    exact (hcarrier 0).mp (by rw [(hq.eq_zero_iff 0).mpr rfl]; exact zero_le_one)
  · let b : R := ‖a‖⁻¹ • a
    have hb : ‖b‖ = 1 := by
      change ‖‖a‖⁻¹ • a‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg a)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha₀)]
    have hbx : b • x ∈ Metric.closedBall (0 : X) r := by
      rw [← hcircled b hb]
      exact smul_mem_smul_set hx
    have hqbx : centeredBallGauge r (b • x) ≤ 1 := (hcarrier _).mpr hbx
    have hback : ‖a‖ • (b • x) = a • x := by
      change ‖a‖ • ((‖a‖⁻¹ • a) • x) = a • x
      rw [← smul_assoc, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha₀), one_smul]
    rw [← hback]
    apply (hcarrier _).mp
    rw [hq.smul_nonneg ‖a‖ (norm_nonneg a)]
    exact (mul_le_of_le_one_left (hq.nonneg (b • x)) ha).trans hqbx

end
end BanachIsometric.MetricGeometry

