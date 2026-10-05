import Posets.AlspachCounterexampleRankLocal

/-! Exact Cantor–Bendixson rank reduction for compact pointed grafts.
At the common last rank of the spines, precisely the base remains. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u v w z
namespace Posets
variable {K : Type v} {I : Type w} [TopologicalSpace K] [T2Space K]
  (anchor : I → K) (X : I → Type z) [∀ i, TopologicalSpace (X i)]
  [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] (p : ∀ i, X i)

theorem alspachCompactGraft_ordinalDerived_eq_base (β : Ordinal.{u})
    (hβ : ∀ i, ordinalDerived (univ : Set (X i)) β = {p i})
    (ha : Function.Surjective anchor) :
    ordinalDerived (univ : Set (AlspachGraft anchor (fun i => {x : X i // x ≠ p i}))) β =
      range (alspachGraftBase anchor _) := by
  apply Subset.antisymm
  · intro x hx
    rcases alspachGraft_cases anchor (fun i => {x : X i // x ≠ p i}) x with
      ⟨k, rfl⟩ | ⟨⟨i, z⟩, rfl⟩
    · exact mem_range_self k
    · have hopen : IsOpenEmbedding (fun z : {x : X i // x ≠ p i} =>
          alspachGraftSpine anchor (fun i => {x : X i // x ≠ p i}) ⟨i, z⟩) :=
        (alspachGraftSpine_isOpenEmbedding anchor _).comp
          (.of_continuous_injective_isOpenMap continuous_sigmaMk sigma_mk_injective
            isOpenMap_sigmaMk)
      have hz := (alspach_ordinalDerived_openEmbedding_mem hopen β z).mp hx
      have hsub : IsOpenEmbedding (Subtype.val : {x : X i // x ≠ p i} → X i) :=
        (isOpen_compl_singleton : IsOpen ({p i}ᶜ : Set (X i))).isOpenEmbedding_subtypeVal
      have hz' := (alspach_ordinalDerived_openEmbedding_mem hsub β z).mpr hz
      rw [hβ i, mem_singleton_iff] at hz'
      exact (z.property hz').elim
  · rintro x ⟨k, rfl⟩
    obtain ⟨i, rfl⟩ := ha k
    have hp : p i ∈ ordinalDerived (univ : Set (X i)) β := by
      rw [hβ i]; exact mem_singleton _
    have he := ordinalDerived_image_closedEmbedding
      (alspachCompactGraftAttach_isClosedEmbedding anchor X p i) univ β
    have hm : alspachCompactGraftAttach anchor X p i (p i) ∈
        ordinalDerived (alspachCompactGraftAttach anchor X p i '' univ) β := by
      rw [he]; exact mem_image_of_mem _ hp
    simpa only [alspachCompactGraftAttach_root] using
      ordinalDerived_mono (subset_univ _) β hm

end Posets
