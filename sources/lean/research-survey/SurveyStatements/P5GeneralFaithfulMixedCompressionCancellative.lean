import SurveyStatements.P5GeneralFaithfulMixedCompression
import SurveyStatements.P5GeneralFaithfulMixedCompressionWitnesses
import SurveyStatements.P5HaarDiagonalBounds

/-! Arbitrary compression coordinates on the actual doubly zero-mean space,
with the genuine norm-one retraction maps. -/

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
variable {Fo Fi : BiTree.SignedTree} {hp : p ≠ ∞}

def generalMixedCancellativeExtension
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (DoublyZeroMean 𝕜 p).subtypeL.comp (T.comp (cancellativeProjection 𝕜 p))

theorem generalMixedCancellativeExtension_apply
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (x : DoublyZeroMean 𝕜 p) : generalMixedCancellativeExtension T x.val = (T x).val := by
  have hfix : cancellativeProjection 𝕜 p x.val = x :=
    congrArg (fun L : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p => L x)
      (cancellativeProjection_retraction 𝕜 p)
  change (T (cancellativeProjection 𝕜 p x.val)).val = _
  rw [hfix]

theorem faithfulMixed_arbitrary_cancellative_compression_coordinate
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (I J K L : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p I J
      (((D.A Fo.faithful Fi.faithful).comp T).comp D.B
        (cancellativeHaar 𝕜 p K L)) =
      faithfulMixedBlockReader (𝕜 := 𝕜) (p := p) Fo Fi I J
        (generalMixedCancellativeExtension T
          (tensorWith ((Fi.block L).vector 𝕜 ⟨1, le_rfl⟩)
            ((Fo.block K).vector 𝕜 ⟨p, Fact.out⟩))) := by
  have h := faithfulMixed_arbitrary_compression_coordinate D Os
    (generalMixedCancellativeExtension T) I J K L
  change productHaarCoordinate 𝕜 p I J
      (D.rawA (generalMixedCancellativeExtension T
        (D.B (cancellativeHaar 𝕜 p K L)).val)) = _ at h
  rw [generalMixedCancellativeExtension_apply] at h
  exact h

theorem exists_faithful_arbitrary_compression_coordinates (hp : p ≠ ∞)
    (Fo Fi : BiTree.SignedTree)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) :
    ∃ A B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) ∧
      ∀ I J K L, cancellativeHaarCoordinate 𝕜 p I J
        (((A.comp T).comp B) (cancellativeHaar 𝕜 p K L)) =
        faithfulMixedBlockReader (𝕜 := 𝕜) (p := p) Fo Fi I J
          (generalMixedCancellativeExtension T
            (tensorWith ((Fi.block L).vector 𝕜 ⟨1, le_rfl⟩)
              ((Fo.block K).vector 𝕜 ⟨p, Fact.out⟩))) := by
  let D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp :=
    Classical.choice (generalMixed_data_exists (𝕜 := 𝕜) (p := p) hp Fo Fi)
  let Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp :=
    Classical.choice (generalMixed_outer_maps_exist (𝕜 := 𝕜) (p := p) hp Fo)
  exact ⟨D.A Fo.faithful Fi.faithful, D.B, D.norm_A Fo.faithful Fi.faithful,
    D.norm_B, D.retraction Fo.faithful Fi.faithful,
    faithfulMixed_arbitrary_cancellative_compression_coordinate (𝕜 := 𝕜) (p := p) D Os T⟩

end SurveyStatements.P5
