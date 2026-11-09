import SurveyStatements.P5OperatorReductionPacketMatrixBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The coarse matrix variance actually tends to zero for finite p > 1.
Actual dyadic refinement preserves the parent and makes its cardinal grow. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Classical ENNReal

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem packetMatrix_one_lt_toReal (p : BanachExponent) (hp : p.val ≠ ∞)
    (hp1 : 1 < p.val) : 1 < p.val.toReal := by
  have h := (ENNReal.toReal_lt_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞) hp).mpr hp1
  simpa only [ENNReal.toReal_one] using h

theorem packetMatrix_variance_bound_tendsto_zero
    (p : BanachExponent) (hp1 : 1 < p.val.toReal)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) :
    Tendsto (fun N : ℕ => 72 * ‖Q‖ ^ 2 * (N : ℝ) ^ (1 / p.val.toReal - 1))
      atTop (𝓝 0) := by
  have hr : 1 / p.val.toReal < 1 :=
    (div_lt_iff₀ (show 0 < p.val.toReal by linarith)).mpr (by simpa using hp1)
  have hδ : 0 < 1 - 1 / p.val.toReal := sub_pos.mpr hr
  have hsmall := (tendsto_rpow_neg_atTop hδ).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hexp : -(1 - 1 / p.val.toReal) = 1 / p.val.toReal - 1 := by ring
  simpa only [hexp, mul_zero] using hsmall.const_mul (72 * ‖Q‖ ^ 2)

theorem operatorReductionPacketMatrix_variance_uniform_small
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val.toReal)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ n : ℕ, ∀ S : Finset (Fin (2 ^ n)),
      N₀ ≤ S.card → operatorReductionPacketMatrixVariance p Q n S < ε := by
  have hev := (packetMatrix_variance_bound_tendsto_zero p hp1 Q).eventually
    (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max N 1, by omega, ?_⟩
  intro n S hS
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  exact (operatorReductionPacketMatrix_variance_le_power p hp Q n S hnonempty).trans_lt
    (hN S.card ((Nat.le_max_left N 1).trans hS))

theorem packetMatrix_refine_card (n : ℕ) (S : Finset (Fin (2 ^ n))) (d : ℕ) :
    (lpHaarRefine n S d).card = S.card * 2 ^ d := by
  have hrad : intervalLpDyadicRadius (n + d) =
      intervalLpDyadicRadius n * intervalLpDyadicRadius d := by
    simp only [intervalLpDyadicRadius, pow_add]
  have hprod : ((S.card * 2 ^ d : ℕ) : ℝ) * intervalLpDyadicRadius (n + d) =
      (S.card : ℝ) * intervalLpDyadicRadius n := by
    rw [Nat.cast_mul, hrad]
    calc
      _ = ((S.card : ℝ) * intervalLpDyadicRadius n) *
          (((2 ^ d : ℕ) : ℝ) * intervalLpDyadicRadius d) := by ring
      _ = _ := by rw [lpHaarRadius_cancel, mul_one]
  have heq := mul_right_cancel₀ (intervalLpDyadicRadius_pos (n + d)).ne'
    ((lpHaarRefine_mass n S d).trans hprod.symm)
  exact_mod_cast heq

theorem packetMatrix_refine_nonempty (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (hS : S.Nonempty) (d : ℕ) : (lpHaarRefine n S d).Nonempty := by
  apply Finset.card_pos.mp
  rw [packetMatrix_refine_card]
  exact Nat.mul_pos (Finset.card_pos.mpr hS) (pow_pos (by norm_num) _)

theorem packetMatrix_refine_card_tendsto_atTop (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty) :
    Tendsto (fun d => (lpHaarRefine n S d).card) atTop atTop := by
  apply tendsto_atTop_mono (fun d => ?_) tendsto_id
  rw [packetMatrix_refine_card]
  apply (Nat.lt_two_pow_self (n := d)).le.trans
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hS
  simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ d) hcard

theorem operatorReductionPacketMatrix_refinement_variance_tendsto_zero
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val.toReal)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty) :
    Tendsto (fun d => operatorReductionPacketMatrixVariance p Q (n + d)
      (lpHaarRefine n S d)) atTop (𝓝 0) := by
  have hbound := (packetMatrix_variance_bound_tendsto_zero p hp1 Q).comp
    (packetMatrix_refine_card_tendsto_atTop n S hS)
  exact squeeze_zero (fun d => operatorReductionPacketMatrixVariance_nonneg p Q _ _)
    (fun d => operatorReductionPacketMatrix_variance_le_power p hp Q _ _
      (packetMatrix_refine_nonempty n S hS d)) hbound

theorem operatorReductionPacketMatrix_variance_uniform_small_of_exponent
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ n : ℕ, ∀ S : Finset (Fin (2 ^ n)),
      N₀ ≤ S.card → operatorReductionPacketMatrixVariance p Q n S < ε :=
  operatorReductionPacketMatrix_variance_uniform_small p hp
    (packetMatrix_one_lt_toReal p hp hp1) Q hε

theorem operatorReductionPacketMatrix_exists_refinement_small
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m ≥ N, ∃ T : Finset (Fin (2 ^ m)), T.Nonempty ∧
      lpHaarBlockParent m T = lpHaarBlockParent n S ∧
      operatorReductionPacketMatrixVariance p Q m T < ε := by
  have hev := (operatorReductionPacketMatrix_refinement_variance_tendsto_zero p hp
    (packetMatrix_one_lt_toReal p hp hp1) Q n S hS).eventually (gt_mem_nhds hε)
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp hev
  let d := max d₀ N
  refine ⟨n + d, by dsimp [d]; omega, lpHaarRefine n S d,
    packetMatrix_refine_nonempty n S hS d, lpHaarBlockParent_refine n S d, ?_⟩
  exact hd₀ d (Nat.le_max_left _ _)

/-- The variance estimate is uniform over every actual operator in a fixed
operator-norm ball. The operator may change with the packet depth. -/
theorem operatorReductionPacketMatrix_variance_le_power_norm_bound
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (C : ℝ) (hQ : ‖Q‖ ≤ C)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty) :
    operatorReductionPacketMatrixVariance p Q n S ≤
      72 * C ^ 2 * (S.card : ℝ) ^ (1 / p.val.toReal - 1) := by
  have hC : 0 ≤ C := (norm_nonneg Q).trans hQ
  have hsq : ‖Q‖ ^ 2 ≤ C ^ 2 := (sq_le_sq₀ (norm_nonneg Q) hC).mpr hQ
  exact (operatorReductionPacketMatrix_variance_le_power p hp Q n S hS).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 72))
      (Real.rpow_nonneg (Nat.cast_nonneg S.card) _))

theorem packetMatrix_variance_constant_bound_tendsto_zero
    (p : BanachExponent) (hp1 : 1 < p.val.toReal) (C : ℝ) :
    Tendsto (fun N : ℕ => 72 * C ^ 2 * (N : ℝ) ^ (1 / p.val.toReal - 1))
      atTop (𝓝 0) := by
  have hr : 1 / p.val.toReal < 1 :=
    (div_lt_iff₀ (show 0 < p.val.toReal by linarith)).mpr (by simpa using hp1)
  have hδ : 0 < 1 - 1 / p.val.toReal := sub_pos.mpr hr
  have hsmall := (tendsto_rpow_neg_atTop hδ).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hexp : -(1 - 1 / p.val.toReal) = 1 / p.val.toReal - 1 := by ring
  simpa only [hexp, mul_zero] using hsmall.const_mul (72 * C ^ 2)

theorem operatorReductionPacketMatrix_variance_uniform_small_norm_bound
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ n : ℕ, ∀ S : Finset (Fin (2 ^ n)),
      ∀ Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p,
      ‖Q‖ ≤ C → N₀ ≤ S.card → operatorReductionPacketMatrixVariance p Q n S < ε := by
  have hev := (packetMatrix_variance_constant_bound_tendsto_zero p
    (packetMatrix_one_lt_toReal p hp hp1) C).eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max N 1, by omega, ?_⟩
  intro n S Q hQ hS
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  exact (operatorReductionPacketMatrix_variance_le_power_norm_bound p hp Q C hQ n S
    hnonempty).trans_lt (hN S.card ((Nat.le_max_left N 1).trans hS))

/-- All sufficiently fine refinements work simultaneously for a finite
family, including families whose actual operators vary with the absolute
refinement level. This permits evaluation on any sufficiently deep reservoir. -/
theorem operatorReductionPacketMatrix_refinement_family_sum_eventually_small
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    {r : ℕ} (Q : ℕ → Fin r → (IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p))
    (C : ℝ) (hQ : ∀ m i, ‖Q m i‖ ≤ C)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d in atTop,
      (∑ i : Fin r, operatorReductionPacketMatrixVariance p (Q (n + d) i) (n + d)
        (lpHaarRefine n S d)) < ε ^ 2 := by
  let δ : ℝ := ε ^ 2 / ((r : ℝ) + 1)
  have hden : 0 < (r : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) hden
  obtain ⟨N₀, _, huniform⟩ :=
    operatorReductionPacketMatrix_variance_uniform_small_norm_bound
      (𝕜 := 𝕜) p hp hp1 C hδ
  filter_upwards [(packetMatrix_refine_card_tendsto_atTop n S hS).eventually
    (eventually_ge_atTop N₀)] with d hd
  calc
    _ ≤ ∑ _i : Fin r, δ := Finset.sum_le_sum (fun i _ =>
      (huniform (n + d) (lpHaarRefine n S d) (Q (n + d) i) (hQ (n + d) i) hd).le)
    _ = (r : ℝ) * δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ((r : ℝ) + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε ^ 2 := by
      dsimp [δ]
      field_simp [hden.ne']

theorem operatorReductionPacketMatrix_exists_refinement_family_sum_small
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    {r : ℕ} (Q : ℕ → Fin r → (IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p))
    (C : ℝ) (hQ : ∀ m i, ‖Q m i‖ ≤ C)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m ≥ N, ∃ T : Finset (Fin (2 ^ m)), T.Nonempty ∧
      lpHaarBlockParent m T = lpHaarBlockParent n S ∧
      (∑ i : Fin r, operatorReductionPacketMatrixVariance p (Q m i) m T) < ε ^ 2 := by
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp
    (operatorReductionPacketMatrix_refinement_family_sum_eventually_small
      p hp hp1 Q C hQ n S hS hε)
  let d := max d₀ N
  refine ⟨n + d, by dsimp [d]; omega, lpHaarRefine n S d,
    packetMatrix_refine_nonempty n S hS d, lpHaarBlockParent_refine n S d, ?_⟩
  exact hd₀ d (Nat.le_max_left _ _)

end SurveyStatements.P5OperatorReduction
