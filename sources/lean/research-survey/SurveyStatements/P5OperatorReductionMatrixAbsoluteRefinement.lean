import SurveyStatements.P5OperatorReductionInnerMatrixVariance
import SurveyStatements.P5Support.LpHaarParentSelection

/-! Absolute-level parent refinements grow along every increasing reservoir.
The moment thresholds are uniform over actual operators in a norm ball. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Classical ENNReal

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem packetMatrix_refineAt_card (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀)))
    (n : ℕ) (hn : n₀ ≤ n) :
    (lpHaarRefineAt n₀ S n).card = S.card * 2 ^ (n - n₀) := by
  unfold lpHaarRefineAt
  simp only [dif_pos hn]
  have htransport (m l : ℕ) (h : m = l) (A : Finset (Fin (2 ^ m))) :
      (h ▸ A).card = A.card := by
    cases h
    rfl
  exact (htransport (n₀ + (n - n₀)) n (Nat.add_sub_of_le hn)
    (lpHaarRefine n₀ S (n - n₀))).trans (packetMatrix_refine_card n₀ S (n - n₀))

theorem packetMatrix_refineAt_nonempty (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀)))
    (hS : S.Nonempty) (n : ℕ) (hn : n₀ ≤ n) :
    (lpHaarRefineAt n₀ S n).Nonempty := by
  apply Finset.card_pos.mp
  rw [packetMatrix_refineAt_card n₀ S n hn]
  exact Nat.mul_pos (Finset.card_pos.mpr hS) (pow_pos (by norm_num) _)

theorem packetMatrix_refineAt_card_tendsto_atTop (n₀ : ℕ)
    (S : Finset (Fin (2 ^ n₀))) (hS : S.Nonempty) :
    Tendsto (fun n => (lpHaarRefineAt n₀ S n).card) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (n₀ + b)] with n hn
  have hn₀ : n₀ ≤ n := by omega
  rw [packetMatrix_refineAt_card n₀ S n hn₀]
  have hb : b ≤ n - n₀ := by omega
  apply hb.trans ((Nat.lt_two_pow_self (n := n - n₀)).le.trans ?_)
  simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ (n - n₀))
    (show 1 ≤ S.card from Finset.card_pos.mpr hS)

theorem packetMatrix_refineAt_reservoir_card_tendsto_atTop (n₀ : ℕ)
    (S : Finset (Fin (2 ^ n₀))) (hS : S.Nonempty)
    (a : ℕ → ℕ) (ha : StrictMono a) :
    Tendsto (fun k => (lpHaarRefineAt n₀ S (a k)).card) atTop atTop :=
  (packetMatrix_refineAt_card_tendsto_atTop n₀ S hS).comp ha.tendsto_atTop

/-- At every sufficiently deep absolute reservoir level, every finite
family in the fixed operator-norm ball satisfies the same small-moment bound. -/
theorem operatorReductionPacketMatrix_refineAt_family_sum_uniform_small
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (C : ℝ) (r : ℕ) (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀))) (hS : S.Nonempty)
    (a : ℕ → ℕ) (ha : StrictMono a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ Q : Fin r → (IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p),
      (∀ i, ‖Q i‖ ≤ C) →
      (∑ i, operatorReductionPacketMatrixVariance p (Q i) (a k)
        (lpHaarRefineAt n₀ S (a k))) < ε := by
  let δ : ℝ := ε / ((r : ℝ) + 1)
  have hden : 0 < (r : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨N₀, _, huniform⟩ :=
    operatorReductionPacketMatrix_variance_uniform_small_norm_bound
      (𝕜 := 𝕜) p hp hp1 C hδ
  filter_upwards [(packetMatrix_refineAt_reservoir_card_tendsto_atTop n₀ S hS a ha).eventually
    (eventually_ge_atTop N₀)] with k hk
  intro Q hQ
  calc
    _ ≤ ∑ _i : Fin r, δ := Finset.sum_le_sum (fun i _ =>
      (huniform (a k) (lpHaarRefineAt n₀ S (a k)) (Q i) (hQ i) hk).le)
    _ = (r : ℝ) * δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ((r : ℝ) + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by dsimp [δ]; field_simp [hden.ne']

theorem operatorReductionInnerMatrix_refineAt_family_sum_uniform_small
    (C : ℝ) (r : ℕ) (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀))) (hS : S.Nonempty)
    (a : ℕ → ℕ) (ha : StrictMono a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      ∀ Q : Fin r → (IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
        IntervalLp 𝕜 operatorReductionL1Exponent), (∀ i, ‖Q i‖ ≤ C) →
      (∑ i, operatorReductionInnerMatrixVariance (Q i) (a k)
        (lpHaarRefineAt n₀ S (a k))) < ε := by
  let δ : ℝ := ε / ((r : ℝ) + 1)
  have hden : 0 < (r : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨N₀, _, huniform⟩ :=
    operatorReductionInnerMatrix_variance_uniform_small_norm_bound (𝕜 := 𝕜) C hδ
  filter_upwards [(packetMatrix_refineAt_reservoir_card_tendsto_atTop n₀ S hS a ha).eventually
    (eventually_ge_atTop N₀)] with k hk
  intro Q hQ
  calc
    _ ≤ ∑ _i : Fin r, δ := Finset.sum_le_sum (fun i _ =>
      (huniform (a k) (lpHaarRefineAt n₀ S (a k)) (Q i) (hQ i) hk).le)
    _ = (r : ℝ) * δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ((r : ℝ) + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by dsimp [δ]; field_simp [hden.ne']

theorem operatorReductionPacketMatrix_refineAt_family_sum_tendsto_zero
    (p : BanachExponent) (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    {r : ℕ} (Q : ℕ → Fin r → (IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p))
    (C : ℝ) (hQ : ∀ k i, ‖Q k i‖ ≤ C)
    (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀))) (hS : S.Nonempty)
    (a : ℕ → ℕ) (ha : StrictMono a) :
    Tendsto (fun k => ∑ i, operatorReductionPacketMatrixVariance p (Q k i) (a k)
      (lpHaarRefineAt n₀ S (a k))) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun k => hb.trans_le
      (Finset.sum_nonneg (fun i _ => operatorReductionPacketMatrixVariance_nonneg p _ _ _)))
  · intro b hb
    filter_upwards [operatorReductionPacketMatrix_refineAt_family_sum_uniform_small
      (𝕜 := 𝕜) p hp hp1 C r n₀ S hS a ha hb] with k hk
    exact hk (Q k) (hQ k)

theorem operatorReductionInnerMatrix_refineAt_family_sum_tendsto_zero
    {r : ℕ} (Q : ℕ → Fin r → (IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent))
    (C : ℝ) (hQ : ∀ k i, ‖Q k i‖ ≤ C)
    (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀))) (hS : S.Nonempty)
    (a : ℕ → ℕ) (ha : StrictMono a) :
    Tendsto (fun k => ∑ i, operatorReductionInnerMatrixVariance (Q k i) (a k)
      (lpHaarRefineAt n₀ S (a k))) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun k => hb.trans_le
      (Finset.sum_nonneg (fun i _ => operatorReductionInnerMatrixVariance_nonneg _ _ _)))
  · intro b hb
    filter_upwards [operatorReductionInnerMatrix_refineAt_family_sum_uniform_small
      (𝕜 := 𝕜) C r n₀ S hS a ha hb] with k hk
    exact hk (Q k) (hQ k)

end SurveyStatements.P5OperatorReduction
