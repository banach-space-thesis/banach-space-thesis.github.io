import SurveyStatements.P5OperatorReductionTraceNormalization
import SurveyStatements.P5OperatorReductionTraceSelectionMoments
import SurveyStatements.P5OperatorReductionCandidateSplits

/-! Both normalized child trace errors have vanishing signed moments
for an actual fixed physical parent. Finite additivity handles both children. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem normalized_trace_true_deviation (v : LpHaarDyadicSetIndex → 𝕜)
    (S : LpHaarFiniteSplit) :
    normalizedParentTrace v (S.child true) - normalizedParentTrace v S.parent =
      (2 / (unitIntervalMeasure.real S.parent.set : 𝕜)) *
        (v ⟨(S.child true).level, (S.child true).atoms⟩ -
          (2 : 𝕜)⁻¹ * v ⟨S.parent.level, S.parent.atoms⟩) := by
  have hm : (unitIntervalMeasure.real S.parent.set : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr S.parent.mass_pos.ne'
  unfold normalizedParentTrace
  dsimp only [unitIntervalMeasure]
  rw [S.child_mass true]
  push_cast
  field_simp [hm]
  <;> ring

theorem normalized_trace_false_deviation (v : LpHaarDyadicSetIndex → 𝕜)
    (hv : ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
      lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j → v k = v i + v j)
    (S : LpHaarFiniteSplit) :
    normalizedParentTrace v (S.child false) - normalizedParentTrace v S.parent =
      -(normalizedParentTrace v (S.child true) - normalizedParentTrace v S.parent) := by
  have hm : (unitIntervalMeasure.real S.parent.set : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr S.parent.mass_pos.ne'
  have hvalue : v ⟨S.parent.level, S.parent.atoms⟩ =
      v ⟨(S.child true).level, (S.child true).atoms⟩ +
        v ⟨(S.child false).level, (S.child false).atoms⟩ :=
    hv _ _ _ S.children_disjoint S.children_union.symm
  unfold normalizedParentTrace
  dsimp only [unitIntervalMeasure]
  rw [S.child_mass false, S.child_mass true, hvalue]
  push_cast
  field_simp [hm]
  <;> ring

theorem normalized_registered_trace_balance_moment_tendsto_zero
    {d : ∀ n, Fin (2 ^ n) → 𝕜} {r : ℕ → ℕ} {M : ℝ}
    (a : RegisteredDyadicTrace d r M) (hM : 0 ≤ M)
    (P : LpHaarFiniteParent) (s : Bool) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖normalizedParentTrace a.value ((candidateRefinedSplit P n θ).child s) -
        normalizedParentTrace a.value (candidateRefinedSplit P n θ).parent‖ ^ 2))
      atTop (𝓝 0) := by
  have htrue : Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖normalizedParentTrace a.value ((candidateRefinedSplit P n θ).child true) -
        normalizedParentTrace a.value (candidateRefinedSplit P n θ).parent‖ ^ 2))
      atTop (𝓝 0) := by
    have hbase := registered_trace_split_moment_tendsto_zero a hM
      (lpHaarRefineAt P.level P.atoms)
    have ht := signed_second_moment_const_mul_tendsto_zero
      (fun n θ => a.value ⟨n + 1, lpHaarSignedChildAtoms n
        (lpHaarRefineAt P.level P.atoms n) θ⟩ -
        (2 : 𝕜)⁻¹ * a.value ⟨n, lpHaarRefineAt P.level P.atoms n⟩)
      (2 / (unitIntervalMeasure.real P.set : 𝕜)) hbase
    apply ht.congr'
    filter_upwards [eventually_ge_atTop P.level] with n hn
    apply congrArg mean
    funext θ
    rw [normalized_trace_true_deviation,
      candidateRefinedSplit_eq P n hn]
    have hparent := refinedFiniteSplit_parent P n hn θ
    rw [hparent]
    rfl
  cases s
  · apply htrue.congr'
    apply Eventually.of_forall
    intro n
    apply congrArg mean
    funext θ
    rw [normalized_trace_false_deviation a.value a.additive, norm_neg]
  · exact htrue

end SurveyStatements.P5OperatorReduction
