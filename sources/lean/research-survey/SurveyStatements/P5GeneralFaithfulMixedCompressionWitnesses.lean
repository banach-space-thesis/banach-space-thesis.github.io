import SurveyStatements.P5FaithfulMixedData
import SurveyStatements.P5BiTreeStabilizationDefinitions

/-! The actual faithful map witnesses are constructed independently of the
large compression conclusion, keeping their typeclass work shared. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem generalMixed_data_exists (hp : p ≠ ∞) (Fo Fi : BiTree.SignedTree) :
    Nonempty (FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp) :=
  exists_faithfulMixedData (𝕜 := 𝕜) (p := p) Fo.toPartitionTree
    Fi.toPartitionTree hp Fo.faithful Fi.faithful

theorem generalMixed_outer_maps_exist (hp : p ≠ ∞) (Fo : BiTree.SignedTree) :
    Nonempty (FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp) :=
  exists_faithfulTreeMaps (𝕜 := 𝕜) (E := 𝕜) (p := p)
    Fo.toPartitionTree hp Fo.faithful

end SurveyStatements.P5
