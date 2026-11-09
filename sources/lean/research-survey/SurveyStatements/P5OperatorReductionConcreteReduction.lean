import SurveyStatements.P5OperatorReductionConcreteErrorAssembly
import SurveyStatements.P5GeneralMixedErrorCanonicalReduction

/-! Genuine selected finite-step data imply the required norm reduction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open scoped ENNReal
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜]

theorem concrete_multiplier_reduction_of_selected_trees (p : BanachExponent)
    (hp : p.val ≠ ∞)
    (T : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (ha : NormalizedTraceExtensional a)
    (hb : NormalizedTraceExtensional b) {ε : ℝ} (hε : 0 < ε)
    (B : ConcreteNormBudgets 𝕜 p ε) (Fo Fi : BiTree.SignedTree)
    (hsteps : ConcreteTreeSteps p (generalMixedCancellativeExtension T)
      a b B.δo B.δi B.ν Fo Fi) :
    ∃ A B M : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val,
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p.val) ∧
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      IsProductHaarMultiplier M
        (fun I J => concreteCanonicalEntry p (generalMixedCancellativeExtension T) Fo Fi I J I J) ∧
      ‖((A.comp T).comp B) - M‖ < ε := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p.val) := inferInstance
  have hErrors := exists_concrete_error_operators p hp
    (generalMixedCancellativeExtension T) a b ha hb hε B Fo Fi hsteps
  let Eo : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hErrors
  have hEiExists := Classical.choose_spec hErrors
  let Ei : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hEiExists
  have hEmExists := Classical.choose_spec hEiExists
  let Em : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hEmExists
  have hs := Classical.choose_spec hEmExists
  exact faithful_arbitrary_multiplier_reduction_of_matrix hp Fo Fi T Eo Ei Em
    (concreteCanonicalEntry p (generalMixedCancellativeExtension T) Fo Fi)
    ‖Eo‖ ‖Ei‖ ‖Em‖ ε le_rfl le_rfl le_rfl hs.1
    (fun I J K L => rfl) hs.2.1 hs.2.2.1 hs.2.2.2

theorem concrete_multiplier_reduction_of_finite_selections (p : BanachExponent)
    (hp : p.val ≠ ∞)
    (T : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val)
    (a b : NormalizedBlockTrace 𝕜) (ha : NormalizedTraceExtensional a)
    (hb : NormalizedTraceExtensional b) {ε : ℝ} (hε : 0 < ε)
    (B : ConcreteNormBudgets 𝕜 p ε)
    (hinner : ∀ n (ho hi : Fin n → LpHaarFiniteSplit)
      (P : LpHaarFiniteParent) (N : ℕ),
      ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
        ConcreteInnerStep p (generalMixedCancellativeExtension T) a b B.δo B.δi B.ν n ho hi S)
    (houter : ∀ n (ho : Fin n → LpHaarFiniteSplit)
      (hi : Fin (n + 1) → LpHaarFiniteSplit) (P : LpHaarFiniteParent) (N : ℕ),
      ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
        ConcreteOuterStep p (generalMixedCancellativeExtension T) a b B.δo B.δi B.ν n ho hi S) :
    ∃ (A B M : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val)
      (d : DyadicIndex → DyadicIndex → 𝕜),
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p.val) ∧
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ IsProductHaarMultiplier M d ∧
      ‖((A.comp T).comp B) - M‖ < ε := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p.val) := inferInstance
  have hTrees := exists_concrete_trees p (generalMixedCancellativeExtension T)
    a b B.δo B.δi B.ν hinner houter
  let Fo : BiTree.SignedTree := Classical.choose hTrees
  have hFiExists := Classical.choose_spec hTrees
  let Fi : BiTree.SignedTree := Classical.choose hFiExists
  have hs := (Classical.choose_spec hFiExists).2.2
  have hOperators := concrete_multiplier_reduction_of_selected_trees
    p hp T a b ha hb hε B Fo Fi hs
  let A : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hOperators
  have hBExists := Classical.choose_spec hOperators
  let B' : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hBExists
  have hMExists := Classical.choose_spec hBExists
  let M : DoublyZeroMean 𝕜 p.val →L[𝕜] DoublyZeroMean 𝕜 p.val :=
    Classical.choose hMExists
  have hspec := Classical.choose_spec hMExists
  exact ⟨A, B', M,
    (fun I J => concreteCanonicalEntry p (generalMixedCancellativeExtension T) Fo Fi I J I J),
    hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2⟩

end SurveyStatements.P5OperatorReduction
