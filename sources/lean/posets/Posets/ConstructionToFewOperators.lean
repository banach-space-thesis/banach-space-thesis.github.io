import Posets.CZeroFactorization
import Posets.MrowkaIndicators

noncomputable section
attribute [local instance] Classical.propDecidable
open ThesisCommon
namespace Posets

/-- The family asserted by Theorem 1.1 satisfies the actual operator condition
of Definition 6.1. This is a conditional bridge; it does not assert Theorem 1.1. -/
theorem theorem_1_1_implies_fewOperators (𝕜 : Type) [RCLike 𝕜]
    (P : Type*) [PartialOrder P] (hmain : Theorem_1_1 𝕜 P)
    (hP : Nonempty (P ↪o Set (Set ℕ))) :
    ∃ 𝒜 : P → Set (Set ℕ), (∀ t, IsAlmostDisjoint (𝒜 t) ∧ ¬ (𝒜 t).Countable) ∧
      ∃ j : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t),
        FewOperators 𝕜 (fun t => Space 𝕜 (𝒜 t)) j := by
  obtain ⟨𝒜, h𝒜, ι, hiso, _, hcomp, hord, hoff⟩ := hmain hP
  let j : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t) :=
    fun s t => if h : s ≤ t then (ι s t h).toContinuousLinearMap else 0
  refine ⟨𝒜, h𝒜, j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact mrowkaCZero_not_separable 𝕜 (𝒜 t) (h𝒜 t).1 (h𝒜 t).2
  · intro s t hst
    simpa only [j, dif_pos hst] using hiso s t hst
  · intro r s t hrs hst
    simpa only [j, dif_pos hrs, dif_pos hst, dif_pos (hrs.trans hst)] using hcomp r s t hrs hst
  · intro s t hst
    simp only [j, dif_neg hst]
  · intro s t hst T
    obtain ⟨a, S, hS, hT⟩ := hord s t hst T
    exact ⟨a, S, hS.hasSeparableRange, by simpa only [j, dif_pos hst] using hT⟩
  · intro s t hst T
    exact (hoff s t hst T).hasSeparableRange

end Posets
