import SurveyStatements.P5OperatorReductionSignedLpGrowth

/-! The uniform threshold for actual bounded families. No fixed family,
orthogonality, or disjointness assumption occurs. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace SurveyStatements.P5OperatorReduction
open P5Support P5Support.Grothendieck
variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [IsProbabilityMeasure μ] in
theorem norm_signedLp_sum_smul {n : ℕ} (f : Fin n → Lp 𝕜 p μ)
    (c : 𝕜) (θ : Fin n → Bool) :
    ‖∑ i, signedValue (θ i) (c • f i)‖ =
      ‖c‖ * ‖∑ i, signedValue (θ i) (f i)‖ := by
  have hs : (∑ i, signedValue (θ i) (c • f i)) =
      c • ∑ i, signedValue (θ i) (f i) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases θ i <;> simp [signedValue]
  rw [hs, norm_smul]

theorem uniform_signedLp_unit_mean_ratio_small (hp : p ≠ ∞) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, N ≤ n → ∀ f : Fin n → Lp 𝕜 p μ,
        (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ 1) →
          mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (f i)‖) /
            (n : ℝ) < ε := by
  intro ε hε
  obtain ⟨N, hN, hsmall⟩ := uniform_signedLp_tiny_family_mean_small (𝕜 := 𝕜)
    (μ := μ) hp ε hε
  refine ⟨N, hN, fun n hn f hf => ?_⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hN.trans_le hn
  let c : 𝕜 := RCLike.ofReal ((n : ℝ)⁻¹)
  have hc : ‖c‖ = (n : ℝ)⁻¹ := by
    simp only [c, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hnR.le)]
  let g : Fin n → Lp 𝕜 p μ := fun i => c • f i
  have hg (i : Fin n) : ∀ᵐ x ∂μ, ‖g i x‖ ≤ (n : ℝ)⁻¹ := by
    filter_upwards [Lp.coeFn_smul c (f i), hf i] with x hx hb
    change ‖(c • f i) x‖ ≤ _
    rw [hx, Pi.smul_apply, norm_smul, hc]
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hnR.le)).trans_eq (mul_one _)
  have hmean : mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (g i)‖) =
      (n : ℝ)⁻¹ * mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (f i)‖) := by
    dsimp only [g]
    simp_rw [norm_signedLp_sum_smul, hc]
    exact mean_mul_left _ _
  have h := hsmall n hn g hg
  rw [hmean] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem uniform_signedLp_mean_ratio_small (hp : p ≠ ∞)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, N ≤ n → ∀ f : Fin n → Lp 𝕜 p μ,
        (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C) →
          mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (f i)‖) /
            (n : ℝ) < ε := by
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨N, hN, hsmall⟩ := uniform_signedLp_unit_mean_ratio_small (𝕜 := 𝕜)
    (μ := μ) hp (ε / (C + 1)) (div_pos hε hC1)
  refine ⟨N, hN, fun n hn f hf => ?_⟩
  let c : 𝕜 := RCLike.ofReal ((C + 1)⁻¹)
  have hc : ‖c‖ = (C + 1)⁻¹ := by
    simp only [c, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hC1.le)]
  let g : Fin n → Lp 𝕜 p μ := fun i => c • f i
  have hg (i : Fin n) : ∀ᵐ x ∂μ, ‖g i x‖ ≤ 1 := by
    filter_upwards [Lp.coeFn_smul c (f i), hf i] with x hx hb
    change ‖(c • f i) x‖ ≤ _
    rw [hx, Pi.smul_apply, norm_smul, hc]
    calc
      _ ≤ (C + 1)⁻¹ * C := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hC1.le)
      _ ≤ (C + 1)⁻¹ * (C + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hC1.le)
      _ = 1 := inv_mul_cancel₀ hC1.ne'
  have hmean : mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (g i)‖) =
      (C + 1)⁻¹ * mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (f i)‖) := by
    dsimp only [g]
    simp_rw [norm_signedLp_sum_smul, hc]
    exact mean_mul_left _ _
  have h := hsmall n hn g hg
  have heq : mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (g i)‖) /
      (n : ℝ) =
      (mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (f i)‖) /
        (n : ℝ)) / (C + 1) := by
    rw [hmean]
    ring
  rw [heq] at h
  exact (div_lt_div_iff_of_pos_right hC1).mp h

theorem tendsto_signedLp_mean_ratio_zero (hp : p ≠ ∞)
    {C : ℝ} (hC : 0 ≤ C) (f : (n : ℕ) → Fin n → Lp 𝕜 p μ)
    (hf : ∀ n i, ∀ᵐ x ∂μ, ‖f n i x‖ ≤ C) :
    Tendsto (fun n => mean (fun θ : Fin n → Bool =>
      ‖∑ i, signedValue (θ i) (f n i)‖) / (n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => ha.trans_le
      (div_nonneg (mean_nonneg (fun _ => norm_nonneg _)) (Nat.cast_nonneg n)))
  · intro ε hε
    obtain ⟨N, _, hsmall⟩ := uniform_signedLp_mean_ratio_small
      (𝕜 := 𝕜) (μ := μ) hp hC ε hε
    exact eventually_atTop.2 ⟨N, fun n hn => hsmall n hn (f n) (hf n)⟩

end SurveyStatements.P5OperatorReduction
