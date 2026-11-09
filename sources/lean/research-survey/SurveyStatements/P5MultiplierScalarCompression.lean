import SurveyStatements.P5FaithfulMixedCompression
import SurveyStatements.P5BiTreeStabilization
import SurveyStatements.P5BiTreeGeometricBudget
import SurveyStatements.P5StableMultiplierScalarClosure
import SurveyStatements.P5StableMultiplierAccuracy

/-! Actual arbitrarily accurate scalar compression of a bounded Haar
multiplier. The limiting scalar is fixed before choosing the accuracy. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open BiTree
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure FixedScalarMultiplierTreeModel
    (d : DyadicIndex → DyadicIndex → 𝕜) where
  lam : 𝕜
  trees : ∀ ε : ℝ, 0 < ε → ∃ Fo Fi : SignedTree,
    (∀ i j, i < j → (Fo.node i).level < (Fo.node j).level) ∧
    (∀ i j, i < j → (Fi.node i).level < (Fi.node j).level) ∧
    SemiStable (compressedSymbol d Fo Fi) (biTreeAccuracy ε) (ε / 4) ∧
    ‖compressedSymbol d Fo Fi root root - lam‖ < ε / 4

def fixedScalarMultiplierTreeModel (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (hM : 0 ≤ M) (hd : ∀ I J, ‖d I J‖ ≤ M) :
    FixedScalarMultiplierTreeModel d := by
  have h := exists_stabilized_trees (𝕜 := 𝕜) (M := M) d hM hd
  let lam := Classical.choose h
  let mu := Classical.choose (Classical.choose_spec h)
  have htrees := Classical.choose_spec (Classical.choose_spec h)
  refine ⟨lam, ?_⟩
  intro ε hε
  have ht := htrees (biTreeAccuracy ε) (fun i j => biTreeAccuracy_pos hε i j)
    (ε / 4) (by linarith only [hε])
  let Fo := Classical.choose ht
  let Fi := Classical.choose (Classical.choose_spec ht)
  have hprops := Classical.choose_spec (Classical.choose_spec ht)
  exact ⟨Fo, Fi, hprops.1, hprops.2.1, hprops.2.2.1, hprops.2.2.2.1⟩

theorem exists_fixed_scalar_multiplier_compression (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (hT : IsProductHaarMultiplier T d) :
    ∃ lam : 𝕜, ∀ ε : ℝ, 0 < ε →
      ∃ A B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) ∧
        ‖(A.comp T).comp B - lam • ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p)‖ < ε := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hbound : ∀ I J, ‖d I J‖ ≤ ‖T‖ :=
    IsProductHaarMultiplier.symbol_norm_le (𝕜 := 𝕜) (p := p)
      (T := T) (d := d) hp hT
  let model := fixedScalarMultiplierTreeModel (𝕜 := 𝕜) d (norm_nonneg T) hbound
  refine ⟨model.lam, fun ε hε => ?_⟩
  have ht := model.trees ε hε
  let Fo := Classical.choose ht
  let Fi := Classical.choose (Classical.choose_spec ht)
  have hprops := Classical.choose_spec (Classical.choose_spec ht)
  have hc := exists_faithful_multiplier_compression (𝕜 := 𝕜) (p := p)
    hp Fo Fi hprops.1 hprops.2.1 T d hT
  let A : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p := Classical.choose hc
  let B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
    Classical.choose (Classical.choose_spec hc)
  have hcompression := Classical.choose_spec (Classical.choose_spec hc)
  exact ⟨A, B, hcompression.1, hcompression.2.1, hcompression.2.2.1,
    stable_multiplier_accuracy_norm_lt (𝕜 := 𝕜) (p := p) hp
      ((A.comp T).comp B) (compressedSymbol d Fo Fi) hcompression.2.2.2
      hε hprops.2.2.1 model.lam hprops.2.2.2⟩

theorem productHaarMultiplier_scalar_compression (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (hT : IsProductHaarMultiplier T d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p, ∃ lam : 𝕜,
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) ∧
      ‖A‖ * ‖B‖ ≤ 1 + ε ∧
      ‖(A.comp T).comp B - lam • ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p)‖ < ε := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hs := exists_fixed_scalar_multiplier_compression (𝕜 := 𝕜) (p := p) hp T d hT
  let lam := Classical.choose hs
  have hc := Classical.choose_spec hs ε hε
  let A : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p := Classical.choose hc
  let B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
    Classical.choose (Classical.choose_spec hc)
  have hprops := Classical.choose_spec (Classical.choose_spec hc)
  refine ⟨A, B, lam, hprops.2.2.1, ?_, hprops.2.2.2⟩
  have hnorm : ‖A‖ * ‖B‖ ≤ 1 :=
    (mul_le_mul hprops.1 hprops.2.1 (norm_nonneg B) zero_le_one).trans (by norm_num)
  exact hnorm.trans (le_add_of_nonneg_right hε.le)

end SurveyStatements.P5

