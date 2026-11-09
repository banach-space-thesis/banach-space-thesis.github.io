import SurveyStatements.P1BasicSequences
import SurveyStatements.P1Transfer
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
The normalized-difference argument in the strongly summing case. Weak
Cauchyness is tested by the genuine continuous complex dual.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Differences along two index sequences tending to infinity are weakly
null for a weak-Cauchy sequence. -/
theorem weakCauchy_differences_tendsto_zero {s : ℕ → X}
    (hs : IsWeakCauchySequence s) {p q : ℕ → ℕ}
    (hp : Tendsto p atTop atTop) (hq : Tendsto q atTop atTop)
    (f : X →L[ℂ] ℂ) :
    Tendsto (fun n => f (s (p n) - s (q n))) atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (hs f)
  simpa only [map_sub, sub_self] using (hl.comp hp).sub (hl.comp hq)

/-- A positive lower bound for the differences' norms permits normalization
without losing weak nullity. -/
theorem weakCauchy_unitDifferences_tendsto_zero {s : ℕ → X}
    (hs : IsWeakCauchySequence s) {p q : ℕ → ℕ}
    (hp : Tendsto p atTop atTop) (hq : Tendsto q atTop atTop)
    {r : ℝ} (hr : 0 < r) (hlower : ∀ n, r ≤ ‖s (p n) - s (q n)‖)
    (f : X →L[ℂ] ℂ) :
    Tendsto (fun n => f (unitNormalize (s (p n) - s (q n)))) atTop (𝓝 0) := by
  have hdiff := weakCauchy_differences_tendsto_zero hs hp hq f
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hupper : ∀ n, ‖f (unitNormalize (s (p n) - s (q n)))‖ ≤
      r⁻¹ * ‖f (s (p n) - s (q n))‖ := by
    intro n
    simp only [unitNormalize, map_smul, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (inv_le_inv₀ (lt_of_lt_of_le hr (hlower n)) hr).mpr (hlower n)
  have hnorm : Tendsto (fun n => r⁻¹ * ‖f (s (p n) - s (q n))‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hdiff.norm.const_mul r⁻¹
  exact squeeze_zero (fun n => norm_nonneg _) hupper hnorm

theorem weakCauchy_unitDifferences_norm {s : ℕ → X} {p q : ℕ → ℕ}
    {r : ℝ} (hr : 0 < r) (hlower : ∀ n, r ≤ ‖s (p n) - s (q n)‖) :
    ∀ n, ‖unitNormalize (s (p n) - s (q n))‖ = 1 := by
  intro n
  apply norm_unitNormalize
  exact norm_pos_iff.mp (lt_of_lt_of_le hr (hlower n))

end SurveyStatements.P1
