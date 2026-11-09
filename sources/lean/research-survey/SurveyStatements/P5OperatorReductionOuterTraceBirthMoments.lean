import SurveyStatements.P5OperatorReductionInnerShadowTrace
import SurveyStatements.P5OperatorReductionRawReaderMoments
import SurveyStatements.P5OperatorReductionOneSidedTraceMoments
import SurveyStatements.P5OperatorReductionCandidateSplits

/-! The actual universal outer traces are small when exactly one inner
block is fresh. This holds on every old outer parent and both children. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem actualNormalizedOuterTrace_birth_target_moment_tendsto_zero
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (r : ℕ → ℕ) (hr : StrictMono r) (a : UniversalInnerPairRegisteredTraces p T r)
    (B P : LpHaarFiniteParent) (L : LpHaarFiniteSplit) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖actualNormalizedOuterTrace p T a (candidateRefinedSplit P n θ, L) B‖ ^ 2))
      atTop (𝓝 0) := by
  let c : 𝕜 := (unitIntervalMeasure.real B.set : 𝕜)⁻¹
  let S := fun m => lpHaarRefineAt B.level B.atoms (r m)
  let g := L.vector 𝕜 innerSplitExponent
  let y : ℕ → Lp 𝕜 1 unitIntervalMeasure := fun m =>
    c • rawHaarPacketShadow p r S T g m
  have hUI : UniformSmallRestrictions y :=
    uniformSmallRestrictions_smul (uniformSmallRestrictions_rawHaarPacketShadow p hp r S T g) c
  let C : ℝ := ‖c‖ * (‖T‖ * ‖g‖)
  have hC : 0 ≤ C := by positivity
  have hnorm : ∀ m, ‖y m‖ ≤ C := by
    intro m
    change ‖c • rawHaarPacketShadow p r S T g m‖ ≤ C
    rw [norm_smul, ← rawHaarPacketShadowOperator_apply]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
    exact ((rawHaarPacketShadowOperator p r S T m).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right (norm_rawHaarPacketShadowOperator_le p r S T m)
        (norm_nonneg g))
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall (fun _ => hε.trans_le (mean_nonneg (fun _ => sq_nonneg _)))
  · intro ε hε
    obtain ⟨N, hN⟩ := limiting_signedBlockReader_second_moment_small y hUI hC hnorm
      P.mass_pos ε hε
    filter_upwards [eventually_ge_atTop (max N P.level)] with n hn
    have hP : P.level ≤ n := (le_max_right N P.level).trans hn
    apply hN n ((le_max_left N P.level).trans hn)
      (lpHaarRefineAt P.level P.atoms n)
    · exact congrArg (fun U => unitIntervalMeasure.real U)
        (lpHaarRefineAt_parent P.level P.atoms n hP)
    · intro θ
      have hreader : (candidateRefinedSplit P n θ).reader 𝕜 innerSplitExponent =
          lpHaarSignedBlockReader 𝕜 innerSplitExponent n
            (lpHaarRefineAt P.level P.atoms n) θ := by
        rw [candidateRefinedSplit_eq P n hP θ]
        rfl
      simpa only [hreader] using
        normalizedRawShadow_blockReader_tendsto p T r hr a
          (candidateRefinedSplit P n θ, L) B

theorem actualNormalizedOuterTrace_birth_source_moment_tendsto_zero
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (r : ℕ → ℕ) (hr : StrictMono r) (a : UniversalInnerPairRegisteredTraces p T r)
    (B P : LpHaarFiniteParent) (J : LpHaarFiniteSplit) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖actualNormalizedOuterTrace p T a (J, candidateRefinedSplit P n θ) B‖ ^ 2))
      atTop (𝓝 0) := by
  let c : 𝕜 := (unitIntervalMeasure.real B.set : 𝕜)⁻¹
  let S := fun m => lpHaarRefineAt B.level B.atoms (r m)
  let φ : ℕ → (Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜) := fun m =>
    (J.reader 𝕜 innerSplitExponent).comp (c • rawHaarPacketShadowOperator p r S T m)
  let C : ℝ := ‖J.reader 𝕜 innerSplitExponent‖ * (‖c‖ * ‖T‖)
  have hC : 0 ≤ C := by positivity
  have hnorm : ∀ m, ‖φ m‖ ≤ C := by
    intro m
    calc
      _ ≤ ‖J.reader 𝕜 innerSplitExponent‖ * ‖c • rawHaarPacketShadowOperator p r S T m‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖J.reader 𝕜 innerSplitExponent‖ * (‖c‖ * ‖rawHaarPacketShadowOperator p r S T m‖) :=
        by rw [norm_smul]
      _ ≤ C := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_rawHaarPacketShadowOperator_le p r S T m)
          (norm_nonneg c)) (norm_nonneg _)
  have hboundlim : Tendsto (fun n => C ^ 2 * intervalLpDyadicRadius n ^
      (1 / innerSplitExponent.val.toReal)) atTop (𝓝 0) := by
    simpa using (lpHaarDyadic_norm_radius_tendsto_zero innerSplitExponent (by simp)).const_mul (C ^ 2)
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall (fun _ => hε.trans_le (mean_nonneg (fun _ => sq_nonneg _)))
  · intro ε hε
    filter_upwards [eventually_ge_atTop P.level,
      (tendsto_order.mp hboundlim).2 ε hε] with n hn hsmall
    apply lt_of_le_of_lt _ hsmall
    apply limiting_functional_signedBlock_second_moment_le_uniform
      innerSplitExponent (by simp) n (lpHaarRefineAt P.level P.atoms n) φ hC hnorm
    intro θ
    have h := normalizedRawShadow_blockReader_tendsto p T r hr a
      (J, candidateRefinedSplit P n θ) B
    have hvector : (candidateRefinedSplit P n θ).vector 𝕜 innerSplitExponent =
        lpHaarSignedBlock 𝕜 innerSplitExponent n (lpHaarRefineAt P.level P.atoms n) θ := by
      rw [candidateRefinedSplit_eq P n hn θ]
      rfl
    rw [hvector] at h
    change Tendsto (fun m => (J.reader 𝕜 innerSplitExponent)
      (c • rawHaarPacketShadowOperator p r S T m
        (lpHaarSignedBlock 𝕜 innerSplitExponent n (lpHaarRefineAt P.level P.atoms n) θ)))
      atTop (𝓝 (actualNormalizedOuterTrace p T a (J, candidateRefinedSplit P n θ) B))
    convert h using 1
    funext m
    exact congrArg (fun z : Lp 𝕜 1 unitIntervalMeasure =>
      (J.reader 𝕜 innerSplitExponent) (c • z))
      (rawHaarPacketShadowOperator_apply p r S T m
        (lpHaarSignedBlock 𝕜 innerSplitExponent n (lpHaarRefineAt P.level P.atoms n) θ))

end SurveyStatements.P5OperatorReduction
