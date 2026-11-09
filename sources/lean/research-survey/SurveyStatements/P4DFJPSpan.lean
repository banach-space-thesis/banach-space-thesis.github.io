import SurveyStatements.P4DFJPWeakInclusion

/-! Every interpolation vector belongs to the ambient closed span of the
generating set, using the vanishing positive-index norm-ball remainder. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set Metric
open scoped Pointwise

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

namespace DFJPSpace

theorem inclusion_mem_closure_span (D : DFJPGaugeData 𝕜 E) (f : DFJPSpace D) :
    inclusion D f ∈ closure (Submodule.span 𝕜 D.carrier : Set E) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let R : ℝ := ‖f‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hR)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hc : (2 : ℝ) ^ (-(n : ℤ)) < ε / R := by
    simpa only [zpow_neg, zpow_natCast, inv_pow] using hn
  have hcε : R * (2 : ℝ) ^ (-(n : ℤ)) < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hR).mp hc
  have hg : dfjpGauge D.carrier n (inclusion D f) < R := by
    have hg' := gauge_le_norm D f n
    exact lt_of_le_of_lt hg' (by change ‖f‖ < ‖f‖ + 1; linarith)
  obtain ⟨r, hr, hrR, y, ⟨u, ⟨k, hk, rfl⟩, v, ⟨w, hw, rfl⟩, rfl⟩, hy⟩ :=
    exists_lt_of_gauge_lt (dfjpNeighborhood_absorbent D.zero_mem n) hg
  refine ⟨(r * (2 : ℝ) ^ (n : ℤ)) • k, ?_, ?_⟩
  · rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact (Submodule.span 𝕜 D.carrier).smul_mem _ (Submodule.subset_span hk)
  · rw [dist_eq_norm, ← hy]
    change ‖r • ((2 : ℝ) ^ (n : ℤ) • k + (2 : ℝ) ^ (-(n : ℤ)) • w) -
      (r * (2 : ℝ) ^ (n : ℤ)) • k‖ < ε
    rw [smul_add, smul_smul, smul_smul, add_sub_cancel_left,
      norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      (r * (2 : ℝ) ^ (-(n : ℤ))) * ‖w‖ ≤ r * (2 : ℝ) ^ (-(n : ℤ)) := by
        have hw' := mem_closedBall_zero_iff.mp hw
        simpa using mul_le_mul_of_nonneg_left hw' (by positivity :
          0 ≤ r * (2 : ℝ) ^ (-(n : ℤ)))
      _ < R * (2 : ℝ) ^ (-(n : ℤ)) :=
        mul_lt_mul_of_pos_right hrR (zpow_pos two_pos _)
      _ < ε := hcε

end DFJPSpace

end SurveyStatements.P4
