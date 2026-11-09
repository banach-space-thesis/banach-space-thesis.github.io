import SurveyStatements.P5OperatorReductionOuterCoefficientMoments
import SurveyStatements.P5OperatorReductionOuterShadowBounds
import SurveyStatements.P5OperatorReductionOuterShadowBlockTrace
import SurveyStatements.P5OperatorReductionOneSidedTraceMoments
import SurveyStatements.P5OperatorReductionCandidateSplits
import SurveyStatements.P5OperatorReductionSignRestriction

/-! Both actual inner-trace birth values have vanishing full-cube second
moments in the one fresh outer split. Only actual scalar limits of the
uniformly bounded finite shadow operators are used. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem packetWeightedCoefficientSignForm_eq_radius_sum (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) (θ : Fin (2 ^ n) → Bool) :
    operatorReductionOuterCoefficientSignForm p n S y
      (fun i => θ (S.orderEmbOfFin rfl i)) =
      (intervalLpDyadicRadius n : 𝕜) * ∑ k ∈ S,
        signedValue (θ k) (lpHaarDyadicCoefficient 𝕜 p n k y) := by
  rw [operatorReductionOuterCoefficientSignForm_eq_block_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases θ k <;> simp [operatorReductionOuterWeightedCoefficient, signedValue, mul_neg]

theorem packetReader_eq_parentNormalizedWeightedSignForm (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) (θ : Fin (2 ^ n) → Bool) :
    lpHaarSignedBlockReader 𝕜 p n S θ y =
      (unitIntervalMeasure.real (lpHaarBlockParent n S) : 𝕜)⁻¹ *
        operatorReductionOuterCoefficientSignForm p n S y
          (fun i => θ (S.orderEmbOfFin rfl i)) := by
  rw [lpHaarSignedBlockReader_eq_rawWeightedReader p n S θ,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply congrArg (fun z : 𝕜 =>
    (unitIntervalMeasure.real (lpHaarBlockParent n S) : 𝕜)⁻¹ * z)
  exact (rawPacket_weightedReader_eq_signed_coefficients p n S θ y).trans
    (packetWeightedCoefficientSignForm_eq_radius_sum p n S y θ).symm

theorem packetReader_second_moment_eq_weighted_variance (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 p) :
    mean (fun θ : Fin (2 ^ n) → Bool => ‖lpHaarSignedBlockReader 𝕜 p n S θ y‖ ^ 2) =
      ‖(unitIntervalMeasure.real (lpHaarBlockParent n S) : 𝕜)⁻¹‖ ^ 2 *
        operatorReductionOuterCoefficientVariance p n S y := by
  simp_rw [packetReader_eq_parentNormalizedWeightedSignForm p n S y, norm_mul, mul_pow]
  rw [mean_mul_left, mean_sign_restrict_packet S
    (fun θ : Fin S.card → Bool => ‖operatorReductionOuterCoefficientSignForm p n S y θ‖ ^ 2)]
  rfl

theorem refined_packetReader_second_moment_le_norm_bound (p : BanachExponent)
    (hp : p.val ≠ ∞) (P : LpHaarFiniteParent) (n : ℕ) (hn : P.level ≤ n)
    (y : IntervalLp 𝕜 p) (C : ℝ) (hy : ‖y‖ ≤ C) :
    mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖lpHaarSignedBlockReader 𝕜 p n (lpHaarRefineAt P.level P.atoms n) θ y‖ ^ 2) ≤
      ‖(unitIntervalMeasure.real P.set : 𝕜)⁻¹‖ ^ 2 *
        (6 * C ^ 2 * intervalLpDyadicRadius n ^ (1 - 1 / p.val.toReal)) := by
  rw [packetReader_second_moment_eq_weighted_variance,
    lpHaarRefineAt_parent P.level P.atoms n hn]
  exact mul_le_mul_of_nonneg_left
    (operatorReductionOuterCoefficient_variance_le_norm_bound p hp n _ y C hy) (sq_nonneg _)

/-- A new target outer reader paired with a fixed old outer vector has
small actual inner-trace birth value. The parent mass stays fixed. -/
theorem actualNormalizedInnerTrace_birth_target_moment_tendsto_zero (p : BanachExponent)
    (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (B P : LpHaarFiniteParent) (L : LpHaarFiniteSplit) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖actualNormalizedInnerTrace p T (candidateRefinedSplit P n θ, L) B‖ ^ 2))
      atTop (𝓝 0) := by
  let C : ℝ := ‖T‖ * ‖L.vector 𝕜 p‖
  let y (m : ℕ) : IntervalLp 𝕜 p :=
    outerHaarPacketShadow p T (B.level + m)
      (shadowDescendants B.level B.atoms m) (L.vector 𝕜 p)
  have hy (m : ℕ) : ‖y m‖ ≤ C :=
    ((outerHaarPacketShadow p T (B.level + m)
      (shadowDescendants B.level B.atoms m)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_outerHaarPacketShadow_le p T _ _) (norm_nonneg _))
  have ht := (operatorReductionOuterCoefficient_variance_bound_tendsto_zero p hp hp1 C).const_mul
    (‖(unitIntervalMeasure.real P.set : 𝕜)⁻¹‖ ^ 2)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => mean_nonneg (fun _ => sq_nonneg _))) _ ht
  filter_upwards [eventually_ge_atTop P.level] with n hn
  apply signed_second_moment_bound_of_limit
    (fun m θ => (candidateRefinedSplit P n θ).reader 𝕜 p (y m))
    (fun θ => actualNormalizedInnerTrace p T (candidateRefinedSplit P n θ, L) B)
    (fun θ => outerShadow_blockReader_tendsto p T (candidateRefinedSplit P n θ, L) B)
  exact Eventually.of_forall (fun m => by
    simp_rw [candidateRefinedSplit_eq P n hn]
    exact refined_packetReader_second_moment_le_norm_bound p hp P n hn (y m) C (hy m))

/-- A fixed old outer reader paired with a new source outer vector has
small actual inner-trace birth value. The actual finite shadow functionals
remain uniformly bounded before their scalar limits are taken. -/
theorem actualNormalizedInnerTrace_birth_source_moment_tendsto_zero (p : BanachExponent)
    (hp : p.val ≠ ∞)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (B P : LpHaarFiniteParent) (K : LpHaarFiniteSplit) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖actualNormalizedInnerTrace p T (K, candidateRefinedSplit P n θ) B‖ ^ 2))
      atTop (𝓝 0) := by
  let C : ℝ := ‖K.reader 𝕜 p‖ * ‖T‖
  let φ (m : ℕ) : IntervalLp 𝕜 p →L[𝕜] 𝕜 :=
    (K.reader 𝕜 p).comp (outerHaarPacketShadow p T (B.level + m)
      (shadowDescendants B.level B.atoms m))
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hφ (m : ℕ) : ‖φ m‖ ≤ C :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_outerHaarPacketShadow_le p T _ _) (norm_nonneg _))
  have ht : Tendsto (fun n => C ^ 2 * intervalLpDyadicRadius n ^ (1 / p.val.toReal))
      atTop (𝓝 0) := by
    simpa using (lpHaarDyadic_norm_radius_tendsto_zero p hp).const_mul (C ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => mean_nonneg (fun _ => sq_nonneg _))) _ ht
  filter_upwards [eventually_ge_atTop P.level] with n hn
  apply limiting_functional_signedBlock_second_moment_le_uniform p hp n
    (lpHaarRefineAt P.level P.atoms n) φ hC hφ
  intro θ
  have h := outerShadow_blockReader_tendsto p T (K, candidateRefinedSplit P n θ) B
  have hvec : (candidateRefinedSplit P n θ).vector 𝕜 p =
      lpHaarSignedBlock 𝕜 p n (lpHaarRefineAt P.level P.atoms n) θ := by
    rw [candidateRefinedSplit_eq P n hn θ]
    rfl
  rw [hvec] at h
  simpa only [φ, ContinuousLinearMap.comp_apply] using h

end SurveyStatements.P5OperatorReduction
