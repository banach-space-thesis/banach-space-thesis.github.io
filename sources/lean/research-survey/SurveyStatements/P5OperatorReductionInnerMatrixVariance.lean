import SurveyStatements.P5OperatorReductionInnerMatrixColumns
import SurveyStatements.P5OperatorReductionMoments
import SurveyStatements.P5OperatorReductionPacketMatrixRaw

/-! The genuine L1 column estimate gives inverse-cardinality centered
variance for every actual same-level inner operator matrix. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ENNReal BigOperators Classical
open Filter Topology

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

def operatorReductionInnerMatrixVariance
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) : ℝ :=
  mean (fun θ : Fin S.card → Bool =>
    ‖(S.card : 𝕜)⁻¹ * centeredQuadraticForm
      (operatorReductionPacketMatrix operatorReductionL1Exponent Q n S) θ‖ ^ 2)

theorem operatorReductionInnerMatrix_offDiagonalSquareSum_le
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    offDiagonalSquareSum (operatorReductionPacketMatrix operatorReductionL1Exponent Q n S) ≤
      (S.card : ℝ) * ‖Q‖ ^ 2 := by
  apply le_trans _ (operatorReductionInnerMatrix_square_sum_le Q n S)
  unfold offDiagonalSquareSum
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem operatorReductionInnerMatrix_variance_le_inverse_card
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    operatorReductionInnerMatrixVariance Q n S ≤ 2 * ‖Q‖ ^ 2 / (S.card : ℝ) := by
  have hfactor : 2 * ((S.card : ℝ)⁻¹) ^ 2 * ((S.card : ℝ) * ‖Q‖ ^ 2) =
      2 * ‖Q‖ ^ 2 / (S.card : ℝ) := by
    by_cases hN : (S.card : ℝ) = 0
    · simp [hN]
    · field_simp [hN]
      <;> ring
  calc
    _ ≤ 2 * ((S.card : ℝ)⁻¹) ^ 2 *
        offDiagonalSquareSum
          (operatorReductionPacketMatrix operatorReductionL1Exponent Q n S) :=
      normalized_centeredQuadraticForm_variance_le _
    _ ≤ 2 * ((S.card : ℝ)⁻¹) ^ 2 * ((S.card : ℝ) * ‖Q‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (operatorReductionInnerMatrix_offDiagonalSquareSum_le Q n S)
        (by positivity)
    _ = _ := hfactor

theorem operatorReductionInnerMatrix_variance_small_of_card
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) {ε : ℝ} (hε : 0 < ε)
    (hcard : 2 * ‖Q‖ ^ 2 / ε < (S.card : ℝ)) :
    operatorReductionInnerMatrixVariance Q n S < ε := by
  have hN : 0 < (S.card : ℝ) :=
    (div_nonneg (by positivity : 0 ≤ 2 * ‖Q‖ ^ 2) hε.le).trans_lt hcard
  apply (operatorReductionInnerMatrix_variance_le_inverse_card Q n S).trans_lt
  have h := (div_lt_iff₀ hε).mp hcard
  exact (div_lt_iff₀ hN).mpr (by simpa only [mul_comm] using h)

theorem operatorReductionInnerMatrixVariance_nonneg
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    0 ≤ operatorReductionInnerMatrixVariance Q n S :=
  mean_nonneg (fun _ => sq_nonneg _)

theorem operatorReductionInnerMatrixVariance_eq_raw
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    operatorReductionInnerMatrixVariance Q n S =
      mean (fun θ : Fin S.card → Bool =>
        ‖(S.card : 𝕜)⁻¹ * centeredQuadraticForm
          (operatorReductionRawPacketMatrix operatorReductionL1Exponent Q n S) θ‖ ^ 2) :=
  operatorReductionPacketMatrixVariance_eq_raw operatorReductionL1Exponent
    (by norm_num [operatorReductionL1Exponent]) Q n S

theorem operatorReductionInnerMatrix_variance_uniform_small_norm_bound
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ n : ℕ, ∀ S : Finset (Fin (2 ^ n)),
      ∀ Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
        IntervalLp 𝕜 operatorReductionL1Exponent,
      ‖Q‖ ≤ C → N₀ ≤ S.card → operatorReductionInnerMatrixVariance Q n S < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C ^ 2 / ε)
  have hNpos : 0 < N := by
    exact_mod_cast ((div_nonneg (by positivity : 0 ≤ 2 * C ^ 2) hε.le).trans_lt hN)
  refine ⟨N, hNpos, ?_⟩
  intro n S Q hQ hS
  have hC : 0 ≤ C := (norm_nonneg Q).trans hQ
  have hsq : ‖Q‖ ^ 2 ≤ C ^ 2 := (sq_le_sq₀ (norm_nonneg Q) hC).mpr hQ
  apply operatorReductionInnerMatrix_variance_small_of_card Q n S hε
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)) hε.le).trans_lt
      (hN.trans_le (by exact_mod_cast hS))

/-- A norm-bounded family may vary with the absolute refinement level;
every sufficiently fine parent-preserving refinement has small total
second moment. -/
theorem operatorReductionInnerMatrix_refinement_family_sum_eventually_small
    {r : ℕ} (Q : ℕ → Fin r →
      (IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
        IntervalLp 𝕜 operatorReductionL1Exponent))
    (C : ℝ) (hQ : ∀ m i, ‖Q m i‖ ≤ C)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d in atTop,
      (∑ i : Fin r, operatorReductionInnerMatrixVariance (Q (n + d) i) (n + d)
        (lpHaarRefine n S d)) < ε ^ 2 := by
  let δ : ℝ := ε ^ 2 / ((r : ℝ) + 1)
  have hden : 0 < (r : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) hden
  obtain ⟨N₀, _, huniform⟩ :=
    operatorReductionInnerMatrix_variance_uniform_small_norm_bound (𝕜 := 𝕜) C hδ
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

theorem operatorReductionInnerMatrix_exists_refinement_family_sum_small
    {r : ℕ} (Q : ℕ → Fin r →
      (IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
        IntervalLp 𝕜 operatorReductionL1Exponent))
    (C : ℝ) (hQ : ∀ m i, ‖Q m i‖ ≤ C)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m ≥ N, ∃ T : Finset (Fin (2 ^ m)), T.Nonempty ∧
      lpHaarBlockParent m T = lpHaarBlockParent n S ∧
      (∑ i : Fin r, operatorReductionInnerMatrixVariance (Q m i) m T) < ε ^ 2 := by
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp
    (operatorReductionInnerMatrix_refinement_family_sum_eventually_small
      Q C hQ n S hS hε)
  let d := max d₀ N
  refine ⟨n + d, by dsimp [d]; omega, lpHaarRefine n S d,
    packetMatrix_refine_nonempty n S hS d, lpHaarBlockParent_refine n S d, ?_⟩
  exact hd₀ d (Nat.le_max_left _ _)

end SurveyStatements.P5OperatorReduction
