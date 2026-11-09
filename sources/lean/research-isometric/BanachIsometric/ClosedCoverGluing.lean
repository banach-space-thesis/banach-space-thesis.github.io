import Mathlib.Topology.ContinuousMap.Basic

/-! Actual continuous gluing of two subtype maps over a finite closed cover. -/

noncomputable section

namespace BanachIsometric

open Set

theorem exists_continuousMap_glue_closed_cover
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hcover : s ∪ t = univ)
    (f : C(s, Y)) (g : C(t, Y))
    (hagree : ∀ x (hx : x ∈ s) (hy : x ∈ t), f ⟨x, hx⟩ = g ⟨x, hy⟩) :
    ∃ F : C(X, Y), (∀ x : s, F x.val = f x) ∧ (∀ x : t, F x.val = g x) := by
  classical
  have hc : ∀ x, x ∈ s ∨ x ∈ t := by
    intro x
    have hx : x ∈ s ∪ t := by rw [hcover]; exact mem_univ x
    exact hx
  let F : X → Y := fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, (hc x).resolve_left hx⟩
  have hFs : ∀ x (hx : x ∈ s), F x = f ⟨x, hx⟩ := by intro x hx; simp only [F, dif_pos hx]
  have hFt : ∀ x (hx : x ∈ t), F x = g ⟨x, hx⟩ := by
    intro x hx
    by_cases hxs : x ∈ s
    · exact (hFs x hxs).trans (hagree x hxs hx)
    · simp only [F, dif_neg hxs]
  have hcont : Continuous F := by
    apply continuous_iff_isClosed.mpr
    intro C hC
    have heq : F ⁻¹' C =
        (Subtype.val '' (f ⁻¹' C)) ∪ (Subtype.val '' (g ⁻¹' C)) := by
      ext x
      constructor
      · intro hx
        rcases hc x with hxs | hxt
        · left
          exact ⟨⟨x, hxs⟩, by change f ⟨x, hxs⟩ ∈ C; rwa [← hFs x hxs], rfl⟩
        · right
          exact ⟨⟨x, hxt⟩, by change g ⟨x, hxt⟩ ∈ C; rwa [← hFt x hxt], rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · change F x.val ∈ C
          rw [hFs x.val x.property]
          exact hx
        · change F x.val ∈ C
          rw [hFt x.val x.property]
          exact hx
    rw [heq]
    exact (hs.isClosedEmbedding_subtypeVal.isClosedMap _ (hC.preimage f.continuous)).union
      (ht.isClosedEmbedding_subtypeVal.isClosedMap _ (hC.preimage g.continuous))
  exact ⟨⟨F, hcont⟩, fun x => hFs x.val x.property, fun x => hFt x.val x.property⟩

end BanachIsometric
