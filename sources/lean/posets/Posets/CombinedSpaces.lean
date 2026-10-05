import Posets.CombinedTopology
import Posets.TopologyStatements
import PosetsCommon.CZeroHomeomorph
import PosetsCommon.CZeroSigma

noncomputable section
namespace Posets

/-- Lemma 4.5, including the concrete combined family, its homeomorphism,
and both isometric identifications of the C₀ spaces. -/
theorem lemma_4_5_proof (𝕜 : Type) [RCLike 𝕜] (𝒜 : ℕ → Set (Set ℕ)) :
    Lemma_4_5 𝕜 𝒜 := by
  intro h𝒜
  exact ⟨combinedFamily 𝒜, combinedFamily_almostDisjoint 𝒜 h𝒜,
    ⟨combinedHomeomorph 𝒜 h𝒜⟩,
    ⟨ThesisCommon.cZeroHomeomorphIsometryEquiv (combinedHomeomorph 𝒜 h𝒜).symm⟩,
    ⟨ThesisCommon.cZeroSigmaIsometryEquiv (fun n => Mrowka (𝒜 n))⟩⟩

end Posets
