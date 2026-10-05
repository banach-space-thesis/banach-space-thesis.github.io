import PFP.SetMappingStatements
import ThesisCommon.Analysis.CountableBlockIsometries

/-! The full countable-block Lemma 4.19, including finite nonempty blocks. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u v

/-- Lemma 4.19: actual surjective linear isometries for finite-p and c₀ sums. -/
theorem lemma_4_19 (𝕜 : Type*) [RCLike 𝕜]
    (Y : Type v) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (Δ : Type u) [Nonempty Δ] [Countable Δ]
    [TopologicalSpace Δ] [DiscreteTopology Δ] : Lemma_4_19 𝕜 Y Δ := by
  let φ := countableBlockIndexEquiv Δ
  constructor
  · intro p hp
    exact ⟨lpBlockFlattenIsometry p.val
      (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp) φ⟩
  · exact ⟨cZeroBlockFlattenIsometry φ⟩

end PFP
