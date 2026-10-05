import Posets.SeparableCZeroCopy
import Posets.CZeroFactorization

noncomputable section
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The containing c₀ copy from Lemma 4.4 gives literal factorisation, with
bounded maps on both sides, for every separable-range operator into the space. -/
theorem factorsThroughCZero_of_hasSeparableRange (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : E →L[𝕜] Space 𝕜 𝒜) (hT : HasSeparableRange 𝕜 E (Space 𝕜 𝒜) T) :
    FactorsThroughCZero 𝕜 T := by
  let X := LinearMap.range T.toLinearMap
  have hX : TopologicalSpace.SeparableSpace X := hT.separableSpace
  obtain ⟨Y, hXY, _, ⟨e⟩⟩ := lemma_4_4_proof 𝕜 𝒜 h𝒜 X hX
  let T' := T.codRestrict Y (fun x => hXY (show T x ∈ X from ⟨x, rfl⟩))
  refine ⟨e.toContinuousLinearMap.comp T', Y.subtypeL.comp e.symm.toContinuousLinearMap, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact (congrArg Subtype.val (e.symm_apply_apply (T' x))).symm

theorem factorsThroughCZero_iff_hasSeparableRange (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : E →L[𝕜] Space 𝕜 𝒜) :
    FactorsThroughCZero 𝕜 T ↔ HasSeparableRange 𝕜 E (Space 𝕜 𝒜) T :=
  ⟨FactorsThroughCZero.hasSeparableRange, factorsThroughCZero_of_hasSeparableRange h𝒜 T⟩

end Posets
