import Posets.AlspachCounterexampleCompactSpines
import ThesisCommon.Analysis.OrdinalBakerDerived

/-! Transfinite Cantor–Bendixson derivatives are local under open embeddings.
This applies to every punctured spine in the concrete Alspach graft. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u v w
namespace Posets
variable {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

theorem alspach_derivedSet_preimage_openEmbedding {f : X → Y}
    (hf : IsOpenEmbedding f) (A : Set Y) :
    f ⁻¹' derivedSet A = derivedSet (f ⁻¹' A) := by
  ext x
  constructor
  · intro hx
    rw [mem_derivedSet, accPt_iff_nhds]
    intro U hU
    obtain ⟨y, ⟨⟨z, hz, rfl⟩, hyA⟩, hyx⟩ :=
      (accPt_iff_nhds.mp hx) (f '' U) (hf.isOpenMap.image_mem_nhds hU)
    exact ⟨z, ⟨hz, hyA⟩, fun he => hyx (congrArg f he)⟩
  · intro hx
    have h := hf.continuous.image_derivedSet hf.injective
      (mem_image_of_mem f hx)
    exact derivedSet_mono _ _ (image_preimage_subset f A) h

theorem alspach_ordinalDerived_preimage_openEmbedding {f : X → Y}
    (hf : IsOpenEmbedding f) (A : Set Y) (α : Ordinal.{u}) :
    f ⁻¹' ordinalDerived A α = ordinalDerived (f ⁻¹' A) α := by
  induction α using Ordinal.limitRecOn with
  | zero => simp
  | succ α ih =>
      rw [ordinalDerived_succ, alspach_derivedSet_preimage_openEmbedding hf, ih,
        ordinalDerived_succ]
  | limit α hα ih =>
      rw [ordinalDerived_limit _ hα, ordinalDerived_limit _ hα]
      simp only [preimage_iInter]
      exact iInter_congr fun β => iInter_congr fun hβ => ih β hβ

theorem alspach_ordinalDerived_openEmbedding_mem {f : X → Y}
    (hf : IsOpenEmbedding f) (α : Ordinal.{u}) (x : X) :
    f x ∈ ordinalDerived (univ : Set Y) α ↔
      x ∈ ordinalDerived (univ : Set X) α := by
  change x ∈ f ⁻¹' ordinalDerived univ α ↔ _
  rw [alspach_ordinalDerived_preimage_openEmbedding hf, preimage_univ]

end Posets
