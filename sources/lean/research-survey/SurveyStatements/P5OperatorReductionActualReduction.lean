import SurveyStatements.P5OperatorReductionConcreteReduction
import SurveyStatements.P5OperatorReductionConcreteFiniteSelections

/-! Arbitrary operators on the actual doubly cancellative mixed space
admit contractive compression to an actual Haar multiplier. Both trace
families and every finite selection are constructed from the operator. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
open scoped ENNReal Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜]

theorem arbitrary_operator_multiplier_compression (p : BanachExponent)
    (hp : p.val ≠ ∞) (hp1 : 1 < p.val)
    (T : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A B M : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val)
      (d : DyadicIndex → DyadicIndex → 𝕜),
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p.val) ∧
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ IsProductHaarMultiplier M d ∧
      ‖((A.comp T).comp B) - M‖ < ε := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p.val) := inferInstance
  let U : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val :=
    generalMixedCancellativeExtension T
  have hReservoir := exists_universal_operator_trace_reservoir p hp
    (fun pair : LpHaarFiniteSplit × LpHaarFiniteSplit => innerPairOuterSlice p U pair)
  let r : ℕ → ℕ := Classical.choose hReservoir
  have hr : StrictMono r := (Classical.choose_spec hReservoir).1
  let a : UniversalInnerPairRegisteredTraces p U r :=
    Classical.choice (Classical.choose_spec hReservoir).2
  let B : ConcreteNormBudgets 𝕜 p ε := Classical.choice (exists_concrete_norm_budgets 𝕜 p hε)
  exact concrete_multiplier_reduction_of_finite_selections p hp T
    (actualNormalizedOuterTrace p U a) (actualNormalizedInnerTrace p U)
    (fun pair P Q hPQ => actualNormalizedOuterTrace_equal_sets p U a pair P Q hPQ)
    (fun pair P Q hPQ => actualNormalizedInnerTrace_equal_sets p U pair P Q hPQ)
    hε B
    (fun n ho hi P N => exists_actual_concrete_inner_step p hp U r hr a
      B.δo B.δi B.ν B.δo_pos B.δi_pos B.ν_pos n ho hi P N)
    (fun n ho hi P N => exists_actual_concrete_outer_step p hp hp1 U r hr a
      B.δo B.δi B.ν B.δo_pos B.δi_pos B.ν_pos n ho hi P N)

end SurveyStatements.P5OperatorReduction
