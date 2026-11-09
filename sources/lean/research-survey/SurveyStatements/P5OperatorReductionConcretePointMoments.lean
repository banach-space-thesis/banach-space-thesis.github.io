import SurveyStatements.P5OperatorReductionPacketDiagonalErrors
import SurveyStatements.P5OperatorReductionSignRestriction
import SurveyStatements.P5OperatorReductionMatrixAbsoluteRefinement
import SurveyStatements.P5OperatorReductionCandidateSplits
import SurveyStatements.P5OperatorReductionTraceSelectionMoments
import SurveyStatements.P5OperatorReductionConcreteEntrySlices
import SurveyStatements.P5Support.LpHaarNormalizedTraces

/-! The actual signed-block point errors have vanishing second moments.
Centered matrix variance and the deterministic physical-parent trace
limit are both supplied by genuine operator constructions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

def rawPacketDiagonal (p : BanachExponent)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) : 𝕜 :=
  (S.card : 𝕜)⁻¹ * ∑ k ∈ S,
    lpHaarDyadicCoefficient 𝕜 p n k (Q (lpHaarDyadic 𝕜 p n k))

theorem signedBlock_centered_second_moment_eq_variance (p : BanachExponent)
    (hp : p.val ≠ ∞) (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖lpHaarSignedBlockReader 𝕜 p n S θ (Q (lpHaarSignedBlock 𝕜 p n S θ)) -
        rawPacketDiagonal p Q n S‖ ^ 2) = operatorReductionPacketMatrixVariance p Q n S := by
  simp_rw [rawPacketDiagonal, operatorReductionSignedBlock_diagonal_error_eq_centered p Q n S]
  rw [mean_sign_restrict_packet S (fun θ : Fin S.card → Bool =>
    ‖(S.card : 𝕜)⁻¹ * centeredQuadraticForm (operatorReductionRawPacketMatrix p Q n S) θ‖ ^ 2)]
  exact (operatorReductionPacketMatrixVariance_eq_raw p hp Q n S).symm

theorem rawPacketDiagonal_refined_parent (p : BanachExponent)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (P : LpHaarFiniteParent) (n : ℕ) (hn : P.level ≤ n) :
    rawPacketDiagonal p Q n (lpHaarRefineAt P.level P.atoms n) =
      (unitIntervalMeasure.real P.set : 𝕜)⁻¹ *
        lpHaarLevelTrace
          (fun l k => lpHaarDyadicCoefficient 𝕜 p l k (Q (lpHaarDyadic 𝕜 p l k))) n P.set := by
  let S := refinedFiniteSplit P n hn (fun _ => false)
  calc
    _ = lpHaarSplitDiagonal
        (fun l k => lpHaarDyadicCoefficient 𝕜 p l k (Q (lpHaarDyadic 𝕜 p l k))) S := rfl
    _ = _ := by
      rw [lpHaarSplitDiagonal_trace, refinedFiniteSplit_parent P n hn]
      exact div_eq_inv_mul _ _

theorem candidate_point_moment_of_variance_and_trace (p : BanachExponent)
    (hp : p.val ≠ ∞) (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (P : LpHaarFiniteParent) (r : ℕ → ℕ) (hr : StrictMono r) (c : 𝕜)
    (hv : Tendsto (fun k => operatorReductionPacketMatrixVariance p Q (r k)
      (lpHaarRefineAt P.level P.atoms (r k))) atTop (𝓝 0))
    (ht : Tendsto (fun k => (unitIntervalMeasure.real P.set : 𝕜)⁻¹ *
      lpHaarLevelTrace
        (fun n i => lpHaarDyadicCoefficient 𝕜 p n i (Q (lpHaarDyadic 𝕜 p n i)))
        (r k) P.set) atTop (𝓝 c)) :
    Tendsto (fun k => mean (fun θ : Fin (2 ^ r k) → Bool =>
      ‖(candidateRefinedSplit P (r k) θ).reader 𝕜 p
        (Q ((candidateRefinedSplit P (r k) θ).vector 𝕜 p)) - c‖ ^ 2))
      atTop (𝓝 0) := by
  let f (k : ℕ) (θ : Fin (2 ^ r k) → Bool) : 𝕜 :=
    lpHaarSignedBlockReader 𝕜 p (r k) (lpHaarRefineAt P.level P.atoms (r k)) θ
      (Q (lpHaarSignedBlock 𝕜 p (r k) (lpHaarRefineAt P.level P.atoms (r k)) θ)) -
      rawPacketDiagonal p Q (r k) (lpHaarRefineAt P.level P.atoms (r k))
  let b (k : ℕ) := rawPacketDiagonal p Q (r k) (lpHaarRefineAt P.level P.atoms (r k)) - c
  have hf : Tendsto (fun k => mean (fun θ => ‖f k θ‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [f, signedBlock_centered_second_moment_eq_variance p hp] using hv
  have hb : Tendsto b atTop (𝓝 0) := by
    have h := ht.sub_const c
    simp only [sub_self] at h
    apply h.congr'
    filter_upwards [hr.tendsto_atTop.eventually (eventually_ge_atTop P.level)] with k hk
    dsimp only [b]
    rw [rawPacketDiagonal_refined_parent p Q P (r k) hk]
  have hsum := signed_second_moment_add_deterministic_tendsto_zero f b hf hb
  apply hsum.congr'
  filter_upwards [hr.tendsto_atTop.eventually (eventually_ge_atTop P.level)] with k hk
  apply congrArg mean
  funext θ
  rw [candidateRefinedSplit_eq P (r k) hk]
  change ‖f k θ + b k‖ ^ 2 =
    ‖lpHaarSignedBlockReader 𝕜 p (r k) (lpHaarRefineAt P.level P.atoms (r k)) θ
      (Q (lpHaarSignedBlock 𝕜 p (r k) (lpHaarRefineAt P.level P.atoms (r k)) θ)) - c‖ ^ 2
  congr 2
  dsimp only [f, b]
  ring

theorem concrete_outer_point_moment_tendsto_zero (p : BanachExponent)
    (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (r : ℕ → ℕ) (hr : StrictMono r) (a : UniversalInnerPairRegisteredTraces p T r)
    (It Is : LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    Tendsto (fun k => mean (fun θ : Fin (2 ^ r k) → Bool =>
      ‖concreteMixedEntry p T (candidateRefinedSplit P (r k) θ) It
        (candidateRefinedSplit P (r k) θ) Is -
          actualNormalizedOuterTrace p T a (It, Is)
            (candidateRefinedSplit P (r k) θ).parent‖ ^ 2)) atTop (𝓝 0) := by
  let Q := innerPairOuterSlice p T (It, Is)
  have hv := operatorReductionPacketMatrix_refineAt_family_sum_tendsto_zero p hp hp1
    (fun _ (_ : Fin 1) => Q) ‖Q‖ (fun _ _ => le_rfl) P.level P.atoms P.nonempty r hr
  have hv' : Tendsto (fun k => operatorReductionPacketMatrixVariance p Q (r k)
      (lpHaarRefineAt P.level P.atoms (r k))) atTop (𝓝 0) := by simpa using hv
  have ht := ((a (It, Is)).limit P.index).const_mul (unitIntervalMeasure.real P.set : 𝕜)⁻¹
  have hpoint := candidate_point_moment_of_variance_and_trace p hp Q P r hr
    (actualNormalizedOuterTrace p T a (It, Is) P) hv' ht
  apply hpoint.congr'
  filter_upwards [hr.tendsto_atTop.eventually (eventually_ge_atTop P.level)] with k hk
  apply congrArg mean
  funext θ
  have hpθ := refinedFiniteSplit_parent P (r k) hk θ
  rw [← candidateRefinedSplit_eq P (r k) hk θ] at hpθ
  rw [actualNormalizedOuterTrace_equal_sets p T a (It, Is) _ P hpθ]
  rfl

theorem concrete_inner_point_moment_tendsto_zero (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot Os : LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖concreteMixedEntry p T Ot (candidateRefinedSplit P n θ)
        Os (candidateRefinedSplit P n θ) -
          actualNormalizedInnerTrace p T (Ot, Os)
            (candidateRefinedSplit P n θ).parent‖ ^ 2)) atTop (𝓝 0) := by
  let c : 𝕜 := (unitIntervalMeasure.real Ot.parent.set : 𝕜)⁻¹
  let R := innerSliceOperator T (Os.vector 𝕜 p) (splitRawWeight Ot)
    (splitRawWeight_measurable Ot) (splitRawWeight_bound Ot)
  let Q : IntervalLp 𝕜 concreteInnerExponent →L[𝕜] IntervalLp 𝕜 concreteInnerExponent := c • R
  have hv := operatorReductionInnerMatrix_refineAt_family_sum_tendsto_zero
    (fun _ (_ : Fin 1) => Q) ‖Q‖ (fun _ _ => le_rfl) P.level P.atoms P.nonempty
    id strictMono_id
  have hv' : Tendsto (fun n => operatorReductionPacketMatrixVariance concreteInnerExponent Q n
      (lpHaarRefineAt P.level P.atoms n)) atTop (𝓝 0) := by simpa using hv
  let d (n : ℕ) (k : Fin (2 ^ n)) :=
    SurveyStatements.P5L1Variation.haarOperatorDiagonal 𝕜
      (SurveyStatements.P5L1Variation.extendMeanZero 𝕜
        (meanZeroInnerSlice T (Os.vector 𝕜 p) (splitRawWeight Ot)
          (splitRawWeight_measurable Ot) (splitRawWeight_bound Ot))) n k
  have hd : (fun n (k : Fin (2 ^ n)) => lpHaarDyadicCoefficient 𝕜 concreteInnerExponent n k
      (Q (lpHaarDyadic 𝕜 concreteInnerExponent n k))) =
      (fun n (k : Fin (2 ^ n)) => c * d n k) := by
    funext n k
    change lpHaarDyadicCoefficient 𝕜 concreteInnerExponent n k
      (c • innerSliceOperator T (Os.vector 𝕜 p) (splitRawWeight Ot)
        (splitRawWeight_measurable Ot) (splitRawWeight_bound Ot)
        (lpHaarDyadic 𝕜 concreteInnerExponent n k)) = _
    rw [map_smul, smul_eq_mul]
    rw [show d n k = _ from meanZeroInnerSlice_haarDiagonal p T (Os.vector 𝕜 p)
      (splitRawWeight Ot) (splitRawWeight_measurable Ot) (splitRawWeight_bound Ot) n k]
    rfl
  have htrace := innerSliceDyadicTraceValue_full_tendsto p T (Os.vector 𝕜 p)
    (splitRawWeight Ot) (splitRawWeight_measurable Ot) (splitRawWeight_bound Ot) P.index
  have ht : Tendsto (fun n => (unitIntervalMeasure.real P.set : 𝕜)⁻¹ *
      lpHaarLevelTrace (fun l k => lpHaarDyadicCoefficient 𝕜 concreteInnerExponent l k
        (Q (lpHaarDyadic 𝕜 concreteInnerExponent l k))) n P.set) atTop
        (𝓝 (actualNormalizedInnerTrace p T (Ot, Os) P)) := by
    convert (htrace.const_mul c).const_mul (unitIntervalMeasure.real P.set : 𝕜)⁻¹ using 1
    · funext n
      rw [hd, lpHaarLevelTrace_mul]
      rfl
    · apply congrArg (fun z : 𝕜 => 𝓝 z)
      unfold actualNormalizedInnerTrace normalizedParentTrace
      simp only [LpHaarFiniteParent.index]
      change c * ((unitIntervalMeasure.real P.set : 𝕜)⁻¹ * _) =
        (unitIntervalMeasure.real P.set : 𝕜)⁻¹ * (c * _)
      ring
  have hpoint := candidate_point_moment_of_variance_and_trace concreteInnerExponent (by simp)
    Q P id strictMono_id (actualNormalizedInnerTrace p T (Ot, Os) P) hv' ht
  apply hpoint.congr'
  filter_upwards [eventually_ge_atTop P.level] with n hn
  apply congrArg mean
  funext θ
  have hpθ := refinedFiniteSplit_parent P n hn θ
  rw [← candidateRefinedSplit_eq P n hn θ] at hpθ
  rw [actualNormalizedInnerTrace_equal_sets p T (Ot, Os) _ P hpθ,
    concreteMixedEntry_innerOutput p T Ot (candidateRefinedSplit P n θ) Os
      (candidateRefinedSplit P n θ)]
  rfl

end SurveyStatements.P5OperatorReduction
