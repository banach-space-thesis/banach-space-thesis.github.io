import Sigma.Topology
import JLMS.Rudin

/-! Scatteredness of the concrete compactification and its atomic dual. -/
noncomputable section
open Set Topology
namespace SigmaNonprimarity

theorem mrowkaScattered (B : Set (Set Point)) : JLMS.IsScattered (MrowkaBase B) := by
  intro s hs
  by_cases h : ∃ x : Point, Sum.inl x ∈ s
  · obtain ⟨x, hx⟩ := h
    exact ⟨Sum.inl x, hx, {Sum.inl x}, isOpen_base_singleton B x,
      inter_eq_right.mpr (singleton_subset_iff.mpr hx)⟩
  · obtain ⟨p, hp⟩ := hs
    rcases p with x | b
    · exact False.elim (h ⟨x, hp⟩)
    · refine ⟨Sum.inr b, hp, tailNeighborhood B b ∅, isOpen_tail B b ∅, ?_⟩
      ext p
      rcases p with x | c
      · have hx : Sum.inl x ∉ s := fun hx => h ⟨x, hx⟩
        simp [hx]
      · simp only [mem_inter_iff, inr_mem_tail, mem_singleton_iff, Sum.inr.injEq]
        exact ⟨fun h => h.2, fun h => ⟨h.symm ▸ hp, h⟩⟩

theorem onePointScattered {X : Type*} [TopologicalSpace X] (hX : JLMS.IsScattered X) :
    JLMS.IsScattered (OnePoint X) := by
  classical
  intro s hs
  by_cases h : (((↑) : X → OnePoint X) ⁻¹' s).Nonempty
  · obtain ⟨x, hx, U, hU, heq⟩ := hX _ h
    refine ⟨↑x, hx, ((↑) : X → OnePoint X) '' U, OnePoint.isOpen_image_coe.mpr hU, ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hps, y, hy, rfl⟩
      have hyx : y = x := by
        have : y ∈ (((↑) : X → OnePoint X) ⁻¹' s) ∩ U := ⟨hps, hy⟩
        rwa [heq, mem_singleton_iff] at this
      exact congrArg OnePoint.some hyx
    · intro p hp
      have hp' : p = ↑x := hp
      subst p
      have hxU : x ∈ U := by
        have : x ∈ (((↑) : X → OnePoint X) ⁻¹' s) ∩ U := by rw [heq]; rfl
        exact this.2
      exact ⟨hx, x, hxU, rfl⟩
  · have hall : ∀ p ∈ s, p = (OnePoint.infty : OnePoint X) := by
      intro p hp
      induction p using OnePoint.rec with
      | infty => rfl
      | coe x => exact False.elim (h ⟨x, hp⟩)
    obtain ⟨p, hp⟩ := hs
    have hinfty : (OnePoint.infty : OnePoint X) ∈ s := hall p hp ▸ hp
    refine ⟨OnePoint.infty, hinfty, univ, isOpen_univ, ?_⟩
    rw [inter_univ]
    exact Set.Subset.antisymm hall (singleton_subset_iff.mpr hinfty)

theorem auScattered (B : Set (Set Point)) : JLMS.IsScattered (AUCompactum B) :=
  onePointScattered (mrowkaScattered B)

/-- The coordinate set is all of K_B, including its infinity point. -/
theorem auAtomicDualModel {B : Set (Set Point)} (hB : AlmostDisjoint B) :
    Nonempty (JLMS.AtomicDualModel ℝ (AUCompactum B)) := by
  letI := mrowkaT2 hB
  exact JLMS.exists_atomicDualModel (auScattered B)

end SigmaNonprimarity
