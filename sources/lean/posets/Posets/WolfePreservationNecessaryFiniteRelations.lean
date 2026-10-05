import Posets.WolfePreservationNecessaryFiniteRelationsMass
import Posets.WolfePreservationNecessarySingleRelation
import JLMS.OrdinalScattered

/-! A finite closed cover by source-single-valued relations transfers the
full target rank to a Wolfe family. The threshold is the uniform section
mass divided by the number of relations, minus the positivity defect. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u v
namespace Posets
variable {𝕜 L I : Type*} [RCLike 𝕜] [MetricSpace L] [CompactSpace L]
  [Countable L] [Fintype I] [Nonempty I]

local instance wolfeFiniteRelationsDualGroup (κ : Ordinal.{v}) :
    NormedAddCommGroup (JLMS.CZero 𝕜 (OrdinalInterval κ) →L[𝕜] 𝕜) := inferInstance
local instance wolfeFiniteRelationsDualSpace (κ : Ordinal.{v}) :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 (OrdinalInterval κ) →L[𝕜] 𝕜) := inferInstance

theorem wolfe_ordinal_finite_relations_nonempty
    {κ : Ordinal.{v}} (M : JLMS.AtomicDualModel 𝕜 (OrdinalInterval κ))
    (R : I → Set (OrdinalInterval κ × L)) (hR : ∀ i, IsClosed (R i))
    (hunique : ∀ i y x z, (y, x) ∈ R i → (y, z) ∈ R i → x = z)
    (μ : L → WeakDual 𝕜 (JLMS.CZero 𝕜 (OrdinalInterval κ))) (hμ : Continuous μ)
    {A : Set L} (hA : IsClosed A) {d η : ℝ}
    (hdefect : ∀ x ∈ A, ‖WeakDual.toStrongDual (μ x)‖ -
      RCLike.re (μ x (wolfeSourceBlock univ isClopen_univ)) ≤ η)
    (hmass : ∀ x ∈ A, d ≤ wolfeMass M (μ x) (⋃ i, {y | (y, x) ∈ R i}))
    (hpositive : 0 < d / Fintype.card I - η)
    {α : Ordinal.{u}} (hc : α.card ≤ Cardinal.aleph0)
    (hrank : (ordinalDerived A α).Nonempty) :
    (wolfeFamily M (d / Fintype.card I - η) (μ '' A) α).Nonempty := by
  obtain ⟨i, B, hB, hBA, hBrank, hBmass⟩ := wolfe_finite_closed_relations_core M
    (JLMS.scattered_subtype JLMS.scattered_ordinal _) μ hμ R hR hA hdefect hmass α hrank
  have hne : (R i).Nonempty := by
    obtain ⟨x, hx⟩ := hBrank
    have hxB : x ∈ B := by
      simpa using ordinalDerived_antitone hB (show (0 : Ordinal.{u}) ≤ α from bot_le) hx
    by_contra hn
    have he : R i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hm := hBmass x hxB
    simp only [he, mem_empty_iff_false, setOf_false, wolfeMass_empty] at hm
    exact (not_le_of_gt hpositive) hm
  obtain ⟨p, hp⟩ := wolfe_ordinal_single_relation_nonempty M (hR i) hne
    (hunique i) μ hμ hB hBmass hc hBrank
  exact ⟨p, wolfeFamily_mono M le_rfl (image_mono hBA) α hp⟩

end Posets
