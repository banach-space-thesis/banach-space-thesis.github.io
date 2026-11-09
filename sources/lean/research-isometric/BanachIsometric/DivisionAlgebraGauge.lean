import BanachIsometric.MetricBallGauge
import Mathlib.Analysis.Normed.Module.Basic

/-! Minkowski homogeneity over a real normed division algebra, including
opposite quaternions. This avoids the commutative-field restriction of
Mathlib's `gauge_smul` theorem and preserves the original scalar action. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped Pointwise

noncomputable section

variable {R X : Type*} [NormedDivisionRing R] [NormedAlgebra ℝ R]
    [AddCommGroup X] [Module ℝ X] [Module R X] [IsScalarTower ℝ R X]

omit [NormedAlgebra ℝ R] [Module ℝ X] [IsScalarTower ℝ R X] in
theorem balanced_smul_mem_mono_divisionAlgebra {s : Set X} (hs : Balanced R s)
    {a b : R} {x : X} (ha : a • x ∈ s) (hba : ‖b‖ ≤ ‖a‖) : b • x ∈ s := by
  by_cases ha₀ : a = 0
  · have hb₀ : b = 0 := norm_le_zero_iff.mp (by simpa only [ha₀, norm_zero] using hba)
    simpa only [ha₀, hb₀] using ha
  · have hratio : ‖b * a⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact (div_le_one (norm_pos_iff.mpr ha₀)).mpr hba
    have hmem := hs.smul_mem hratio ha
    simpa only [smul_smul, mul_assoc, inv_mul_cancel₀ ha₀, mul_one] using hmem

omit [NormedAlgebra ℝ R] [Module ℝ X] [IsScalarTower ℝ R X] in
theorem balanced_smul_mem_iff_divisionAlgebra {s : Set X} (hs : Balanced R s)
    {a b : R} {x : X} (h : ‖a‖ = ‖b‖) : a • x ∈ s ↔ b • x ∈ s :=
  ⟨fun ha => balanced_smul_mem_mono_divisionAlgebra hs ha h.ge,
    fun hb => balanced_smul_mem_mono_divisionAlgebra hs hb h.le⟩
/-- Equal scalar norms preserve membership in a balanced radial set, so the
infimum defining the gauge is unchanged by replacing a scalar by its norm. -/
theorem gauge_norm_smul_divisionAlgebra {s : Set X} (hs : Balanced R s) (a : R) (x : X) :
    gauge s (‖a‖ • x) = gauge s (a • x) := by
  unfold gauge
  congr with θ
  rw [← algebraMap_smul R ‖a‖ x]
  refine and_congr_right fun _ => balanced_smul_mem_iff_divisionAlgebra (hs.smul _) ?_
  rw [norm_algebraMap', Real.norm_eq_abs, abs_norm]

theorem gauge_smul_divisionAlgebra {s : Set X} (hs : Balanced R s) (a : R) (x : X) :
    gauge s (a • x) = ‖a‖ * gauge s x := by
  rw [← gauge_norm_smul_divisionAlgebra hs a x, gauge_smul_of_nonneg (norm_nonneg a)]
  rfl

variable [MetricSpace X]

theorem centeredBallGauge_smul_divisionAlgebra {r : ℝ}
    (hb : Balanced R (Metric.closedBall (0 : X) r)) (a : R) (x : X) :
    centeredBallGauge r (a • x) = ‖a‖ * centeredBallGauge r x :=
  gauge_smul_divisionAlgebra hb a x

end
end BanachIsometric.MetricGeometry


