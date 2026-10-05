import Posets.AlspachCounterexampleCompactSpines

/-! A closed set missing a base point meets only finitely many punctured
spines attached there. This is the compactness fact behind the common-root
branch elimination in Alspach's Wolfe-index estimate. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology
namespace Posets
variable {K I : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  (anchor : I → K) (X : I → Type*) [∀ i, TopologicalSpace (X i)]

theorem alspachGraft_closed_excludes_base_finite_spines
    (C : Set (AlspachGraft anchor X)) (hC : IsClosed C) (p : K)
    (hp : alspachGraftBase anchor X p ∉ C) :
    ∃ s : Finset I, ∀ i ∉ s, anchor i = p → ∀ x : X i,
      alspachGraftSpine anchor X ⟨i, x⟩ ∉ C := by
  let S : Set (Σ i, X i) := {z | alspachGraftSpine anchor X z ∈ C ∧ anchor z.1 = p}
  have he : alspachGraftSpine anchor X '' S =
      C ∩ {z : AlspachGraft anchor X | z.val.1 = p} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hz
      rcases alspachGraft_cases anchor X z with ⟨k, rfl⟩ | ⟨w, rfl⟩
      · have hk : k = p := hz.2
        subst k
        exact (hp hz.1).elim
      · exact ⟨w, hz, rfl⟩
  have hc : IsCompact S := by
    rw [(alspachGraftSpine_isOpenEmbedding anchor X).isEmbedding.isCompact_iff, he]
    exact (hC.inter (isClosed_eq (continuous_fst.comp continuous_subtype_val)
      continuous_const)).isCompact
  obtain ⟨s, t, hs, _, hst⟩ := IsCompact.sigma_exists_finite_sigma_eq S hc
  refine ⟨hs.toFinset, ?_⟩
  intro i hi hip x hx
  have hm : (⟨i, x⟩ : Σ i, X i) ∈ S := ⟨hx, hip⟩
  rw [← hst] at hm
  exact hi (hs.mem_toFinset.mpr hm.1)

end Posets
