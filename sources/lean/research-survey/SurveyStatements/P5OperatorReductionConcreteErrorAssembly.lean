import SurveyStatements.P5OperatorReductionConcreteTraceBounds
import SurveyStatements.P5OperatorReductionNormBudgets
import SurveyStatements.P5GeneralMixedErrorCanonicalTraceCoordinates
import SurveyStatements.P5GeneralMixedErrorCanonicalNuclear

/-! The concrete selected trees give all three actual small error operators.
No bounded matrix is silently treated as a bounded operator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open scoped ENNReal BigOperators Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜]

def concreteCanonicalEntry (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Fo Fi : BiTree.SignedTree) (I J K L : DyadicIndex) : 𝕜 :=
  concreteMixedEntry p T (Fo.block I) (Fi.block J) (Fo.block K) (Fi.block L)

theorem exists_concrete_error_operators (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (ha : NormalizedTraceExtensional a)
    (hb : NormalizedTraceExtensional b) {ε : ℝ} (hε : 0 < ε)
    (B : ConcreteNormBudgets 𝕜 p ε) (Fo Fi : BiTree.SignedTree)
    (hsteps : ConcreteTreeSteps p T a b B.δo B.δi B.ν Fo Fi) :
    ∃ Eo Ei Em : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val,
      ‖Eo‖ + ‖Ei‖ + ‖Em‖ < ε ∧
      (∀ I J K L, cancellativeHaarCoordinate 𝕜 p.val I J
        (Eo (cancellativeHaar 𝕜 p.val K L)) =
          if I = K ∧ J ≠ L then concreteCanonicalEntry p T Fo Fi K J K L else 0) ∧
      (∀ I J K L, cancellativeHaarCoordinate 𝕜 p.val I J
        (Ei (cancellativeHaar 𝕜 p.val K L)) =
          if I ≠ K ∧ J = L then concreteCanonicalEntry p T Fo Fi I L K L else 0) ∧
      ∀ I J K L, cancellativeHaarCoordinate 𝕜 p.val I J
        (Em (cancellativeHaar 𝕜 p.val K L)) =
          if I ≠ K ∧ J ≠ L then concreteCanonicalEntry p T Fo Fi I J K L else 0 := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p.val) := inferInstance
  let go (q : GeneralMixedStripIndex) (i : ℕ) : 𝕜 :=
    concreteMixedEntry p T (Fo.node i) (Fi.block q.val.1) (Fo.node i) (Fi.block q.val.2)
  let to' (q : GeneralMixedStripIndex) (i : ℕ) : 𝕜 :=
    a (Fi.block q.val.1, Fi.block q.val.2) (Fo.node i).parent
  let gi (q : GeneralMixedStripIndex) (j : ℕ) : 𝕜 :=
    concreteMixedEntry p T (Fo.block q.val.1) (Fi.node j) (Fo.block q.val.2) (Fi.node j)
  let ti (q : GeneralMixedStripIndex) (j : ℕ) : 𝕜 :=
    b (Fo.block q.val.1, Fo.block q.val.2) (Fi.node j).parent
  let do' (q : GeneralMixedStripIndex) := B.δo (stripHeapIndices q).1 (stripHeapIndices q).2
  let di' (q : GeneralMixedStripIndex) := B.δi (stripHeapIndices q).1 (stripHeapIndices q).2
  have ho (q : GeneralMixedStripIndex) := concrete_outer_trace_bounds hsteps ha
    (fun he => q.property (BiTree.heapIndex_injective he))
    (B.δo_pos (stripHeapIndices q).1 (stripHeapIndices q).2).le
  have hi (q : GeneralMixedStripIndex) := concrete_inner_trace_bounds hsteps hb
    (fun he => q.property (BiTree.heapIndex_injective he))
    (B.δi_pos (stripHeapIndices q).1 (stripHeapIndices q).2).le
  have hoExists := exists_generalMixedOuterTraceStripSeries (𝕜 := 𝕜) (p := p.val)
    hp go to' do' (fun q => (B.δo_pos _ _).le)
    (fun q => (ho q).1) (fun q => (ho q).2.1) (fun q => (ho q).2.2)
    (fun q => q.val.1) (fun q => q.val.2) B.bo B.bo_sum B.outer_factor
  let Eo : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hoExists
  have hno : ‖Eo‖ ≤ ∑' q, B.bo q := (Classical.choose_spec hoExists).1
  have hEo := (Classical.choose_spec hoExists).2
  have hiExists := exists_generalMixedInnerTraceStripSeries (𝕜 := 𝕜) (p := p.val)
    hp gi ti di' (fun q => (B.δi_pos _ _).le)
    (fun q => (hi q).1) (fun q => (hi q).2.1) (fun q => (hi q).2.2)
    (fun q => q.val.1) (fun q => q.val.2) B.bi B.bi_sum B.inner_factor
  let Ei : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hiExists
  have hni : ‖Ei‖ ≤ ∑' q, B.bi q := (Classical.choose_spec hiExists).1
  have hEi := (Classical.choose_spec hiExists).2
  have hm : ∀ q : GeneralMixedNuclearIndex,
      ‖concreteCanonicalEntry p T Fo Fi q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2‖ *
        (‖cancellativeHaarCoordinate 𝕜 p.val q.val.2.1 q.val.2.2‖ *
          ‖cancellativeHaar 𝕜 p.val q.val.1.1 q.val.1.2‖) ≤ B.bm q := by
    intro q
    have hq := concrete_mixed_entry_bound hsteps
      (fun he => q.property.1 (BiTree.heapIndex_injective he))
      (fun he => q.property.2 (BiTree.heapIndex_injective he))
    exact (mul_le_mul_of_nonneg_right hq
      (mul_nonneg (ContinuousLinearMap.opNorm_nonneg
        (cancellativeHaarCoordinate 𝕜 p.val q.val.2.1 q.val.2.2))
        (norm_nonneg (cancellativeHaar 𝕜 p.val q.val.1.1 q.val.1.2)))).trans
      (B.mixed_factor q)
  have hmExists := exists_generalMixedCanonicalNuclearError (𝕜 := 𝕜) (p := p.val)
    hp (concreteCanonicalEntry p T Fo Fi) B.bm B.bm_sum hm
  let Em : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hmExists
  have hnm : ‖Em‖ ≤ ∑' q, B.bm q := (Classical.choose_spec hmExists).1
  have hEm := (Classical.choose_spec hmExists).2
  refine ⟨Eo, Ei, Em, ?_, ?_, ?_, hEm⟩
  · have htotal : (∑' q, B.bo q) + (∑' q, B.bi q) + (∑' q, B.bm q) ≤ ε / 2 :=
      (add_le_add (add_le_add B.bo_total B.bi_total) B.bm_total).trans_eq (by ring)
    exact (add_le_add (add_le_add hno hni) hnm).trans_lt
      (htotal.trans_lt (by linarith only [hε]))
  · exact generalMixed_outer_trace_coordinates_of_heap_coefficients Eo
      (concreteCanonicalEntry p T Fo Fi) go hEo (fun q I => rfl)
  · exact generalMixed_inner_trace_coordinates_of_heap_coefficients Ei
      (concreteCanonicalEntry p T Fo Fi) gi hEi (fun q J => rfl)

end SurveyStatements.P5OperatorReduction
