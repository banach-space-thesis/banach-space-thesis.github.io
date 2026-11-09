import SurveyStatements.P5GeneralFaithfulMixedCompressionCancellative
import SurveyStatements.P5GeneralMixedErrorAssembly

/-! Honest assembly interface for the tree construction: genuine small
strip/mixed operators with the exact block-reader coordinates produce the
arbitrary-operator-to-multiplier reduction required by scalar compression. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem faithful_arbitrary_multiplier_reduction_of_errors (hp : p ≠ ∞)
    (Fo Fi : BiTree.SignedTree)
    (T Eouter Einner Emixed : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (Couter Cinner Cmixed δ : ℝ)
    (ho : ‖Eouter‖ ≤ Couter) (hi : ‖Einner‖ ≤ Cinner) (hm : ‖Emixed‖ ≤ Cmixed)
    (hbudget : Couter + Cinner + Cmixed < δ)
    (hcoordinates : ∀ I J K L,
      faithfulMixedBlockReader (𝕜 := 𝕜) (p := p) Fo Fi I J
        (generalMixedCancellativeExtension T
          (tensorWith ((Fi.block L).vector 𝕜 ⟨1, le_rfl⟩)
            ((Fo.block K).vector 𝕜 ⟨p, Fact.out⟩))) =
        cancellativeHaarCoordinate 𝕜 p I J
          (d K L • cancellativeHaar 𝕜 p K L +
            Eouter (cancellativeHaar 𝕜 p K L) +
            Einner (cancellativeHaar 𝕜 p K L) +
            Emixed (cancellativeHaar 𝕜 p K L))) :
    ∃ A B M : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) ∧
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ IsProductHaarMultiplier M d ∧
      ‖((A.comp T).comp B) - M‖ < δ := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hab :=
    exists_faithful_arbitrary_compression_coordinates (𝕜 := 𝕜) (p := p) hp Fo Fi T
  let A : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p := Classical.choose hab
  let B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
    Classical.choose (Classical.choose_spec hab)
  have hprops := Classical.choose_spec (Classical.choose_spec hab)
  have hc : ∀ I J K L,
      cancellativeHaarCoordinate 𝕜 p I J
        (((A.comp T).comp B) (cancellativeHaar 𝕜 p K L)) =
      cancellativeHaarCoordinate 𝕜 p I J
        (d K L • cancellativeHaar 𝕜 p K L +
          Eouter (cancellativeHaar 𝕜 p K L) +
          Einner (cancellativeHaar 𝕜 p K L) +
          Emixed (cancellativeHaar 𝕜 p K L)) :=
    fun I J K L => (hprops.2.2.2 I J K L).trans (hcoordinates I J K L)
  have hm := exists_generalMixed_multiplier_of_error_coordinates
    (𝕜 := 𝕜) (p := p) hp
    ((A.comp T).comp B) Eouter Einner Emixed d Couter Cinner Cmixed ho hi hm hc
  let M : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p := Classical.choose hm
  have hM := Classical.choose_spec hm
  exact ⟨A, B, M, hprops.2.2.1, hprops.1, hprops.2.1, hM.1, hM.2.trans_lt hbudget⟩

end SurveyStatements.P5
