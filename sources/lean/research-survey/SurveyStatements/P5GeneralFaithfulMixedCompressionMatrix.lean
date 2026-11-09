import SurveyStatements.P5GeneralFaithfulMixedCompressionEntries

/-! Full signed matrix expansion: both input atoms and both output atoms
occur for an arbitrary bounded operator, including every off-diagonal entry. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {Fo Fi : BiTree.SignedTree} {hp : p ≠ ∞}

theorem faithfulMixed_arbitrary_compression_matrix_sum
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (I J K L : DyadicIndex) :
    productHaarCoordinate 𝕜 p I J (D.rawA (T (D.rawB (productHaar 𝕜 p K L)))) =
      ∑ l ∈ (Fi.block L).atoms, ∑ k ∈ (Fo.block K).atoms,
        signedValue ((Fi.block L).signs l) (signedValue ((Fo.block K).signs k)
          (((Fo.block I).atoms.card : 𝕜)⁻¹ * ((Fi.block J).atoms.card : 𝕜)⁻¹ *
            ∑ r ∈ (Fo.block I).atoms, ∑ s ∈ (Fi.block J).atoms,
              signedValue ((Fo.block I).signs r) (signedValue ((Fi.block J).signs s)
                (productHaarCoordinate 𝕜 p ⟨(Fo.block I).level, r⟩ ⟨(Fi.block J).level, s⟩
                  (T (productHaar 𝕜 p ⟨(Fo.block K).level, k⟩ ⟨(Fi.block L).level, l⟩)))))) := by
  rw [faithfulMixed_arbitrary_compression_coordinate_sum D Os T]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  rw [faithfulMixedBlockReader_coordinate_sum]

end SurveyStatements.P5
