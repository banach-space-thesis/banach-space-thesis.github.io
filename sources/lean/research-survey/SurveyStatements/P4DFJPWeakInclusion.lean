import SurveyStatements.P4DFPSmallRemainder
import SurveyStatements.P4DFJPBounds

/-!
# Weak compactness of the genuine DFJP inclusion

The interpolation unit ball is in every closed padded neighborhood. The
small-ball term tends to zero, so Goldstine and the closed canonical bidual
image force the inclusion's second adjoint to take values in the ambient
Banach space. Reflexivity of the interpolation space is a further step.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 500000
set_option synthInstance.maxSize 2048

open Set Metric
open scoped Pointwise ENNReal

namespace SurveyStatements.P4

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

lemma paddedNeighborhood_mono_right (K : Set E) (a : ℝ) {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    paddedNeighborhood K a b ⊆ paddedNeighborhood K a c := by
  have hball (r : ℝ) (hr : 0 ≤ r) : r • closedBall (0 : E) 1 = closedBall 0 r := by
    by_cases hzero : r = 0
    · simp [hzero]
      rfl
    · simpa [Real.norm_of_nonneg hr] using (smul_closedBall' hzero (0 : E) (1 : ℝ))
  rw [paddedNeighborhood, paddedNeighborhood, hball b hb, hball c (hb.trans hbc)]
  exact add_subset_add_left (closedBall_subset_closedBall hbc)

namespace DFJPSpace

variable (D : DFJPGaugeData 𝕜 E)

lemma gauge_le_norm (f : DFJPSpace D) (j : ℤ) :
    dfjpGauge D.carrier j (inclusion D f) ≤ ‖f‖ := by
  rw [← coordinate_eq D f j, ← DFJPScale.norm_eq_gauge]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f.val j

lemma unitBall_in_closure_neighborhood (f : DFJPSpace D) (hf : ‖f‖ ≤ 1) (j : ℤ) :
    inclusion D f ∈ closure (dfjpNeighborhood D.carrier j) := by
  exact (gauge_le_one_iff_mem_closure
    ((dfjpNeighborhood_absConvex D.absConvex j).2)
    (dfjpNeighborhood_mem_nhds D.zero_mem j)).mp ((gauge_le_norm D f j).trans hf)

lemma unitBall_smallRemainders
    (hK : IsCompact ((toWeakSpace 𝕜 E) '' D.carrier)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set E, ∃ a : ℝ,
      IsCompact ((toWeakSpace 𝕜 E) '' K) ∧
      ∀ f : DFJPSpace D, ‖f‖ ≤ 1 → inclusion D f ∈ closure (paddedNeighborhood K a ε) := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hn' : (2 : ℝ) ^ (-(n : ℤ)) ≤ ε := by
    simpa only [zpow_neg, zpow_natCast, inv_pow] using hn.le
  refine ⟨D.carrier, (2 : ℝ) ^ (n : ℤ), hK, ?_⟩
  intro f hf
  exact closure_mono (paddedNeighborhood_mono_right D.carrier _
    (le_of_lt (zpow_pos two_pos _)) hn') (unitBall_in_closure_neighborhood D f hf n)

/-- Weak compactness of the actual interpolation inclusion, derived from
Goldstine and the vanishing norm-ball remainder. -/
theorem inclusion_weaklyCompact [CompleteSpace E]
    (hK : IsCompact ((toWeakSpace 𝕜 E) '' D.carrier)) :
    IsWeaklyCompactOperator 𝕜 (inclusion D) := by
  apply weaklyCompact_of_bidual_mem_image (inclusion D)
  intro ξ
  let r : ℝ := ‖ξ‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let a : 𝕜 := r
  have ha : a ≠ 0 := by simpa [a] using hr.ne'
  have hna : ‖a‖ = r := by simp [a, abs_of_pos hr]
  letI : NormSMulClass 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (DFJPSpace D))) :=
    NormedSpace.toNormSMulClass (𝕜 := 𝕜)
      (E := StrongDual 𝕜 (StrongDual 𝕜 (DFJPSpace D)))
  have hξ : ‖a⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hna, ← div_eq_inv_mul]
    apply (div_le_one hr).mpr
    dsimp [r]
    linarith
  have hm := (bidualImage 𝕜 E).smul_mem a
    (bidual_unitBall_mem_image_of_smallRemainders (inclusion D)
      (unitBall_smallRemainders D hK) (a⁻¹ • ξ) hξ)
  simpa only [map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul] using hm

end DFJPSpace

end SurveyStatements.P4
