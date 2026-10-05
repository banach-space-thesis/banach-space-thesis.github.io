import JLMS.MinimalCompactImage
import Mathlib.Topology.Perfect

/-!
# Continuous images and countability of compact scattered spaces

Take a minimal closed set mapping onto a nonempty closed part of the image.
An isolated point in this minimal set must give an isolated image point:
otherwise deleting its open singleton would still cover that image. Applying
this to closures proves scatteredness of a compact continuous image.
Cantor–Bendixson then shows that a second-countable scattered space is countable.
These facts support the separable-image argument for C₀(K) admissibility.
-/

noncomputable section

open Set Filter Topology

namespace JLMS

variable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

theorem exists_isolated_point_of_compact_image [CompactSpace K] [T2Space L]
    (hK : IsScattered K) (f : K → L) (hf : Continuous f)
    (D : Set L) (hD : IsClosed D) (hne : D.Nonempty) (hDrange : D ⊆ range f) :
    ∃ y ∈ D, ∃ V : Set L, IsOpen V ∧ D ∩ V = {y} := by
  obtain ⟨C, hC, hCD, hminimal⟩ := exists_minimal_closed_image f hf D hD hDrange
  have hCne : C.Nonempty := by
    have h := hne
    rw [← hCD] at h
    exact h.of_image
  obtain ⟨x, hxC, U, hU, hCU⟩ := hK C hCne
  have hxU : x ∈ U := by
    have hx : x ∈ C ∩ U := by rw [hCU]; exact mem_singleton x
    exact hx.2
  let C' := C \ U
  have hC' : IsClosed C' := hC.inter hU.isClosed_compl
  have hproper : f '' C' ≠ D := by
    intro heq
    have h := hminimal C' diff_subset hC' heq
    have hx : x ∈ C' := h.symm ▸ hxC
    exact hx.2 hxU
  have hsub : f '' C' ⊆ D := hCD ▸ image_mono diff_subset
  have hnsub : ¬D ⊆ f '' C' := fun h => hproper (Subset.antisymm hsub h)
  obtain ⟨y, hyD, hyout⟩ := not_subset.mp hnsub
  let V := (f '' C')ᶜ
  have hV : IsOpen V := (hC'.isCompact.image hf).isClosed.isOpen_compl
  have huniq (z : L) (hz : z ∈ D ∩ V) : z = f x := by
    have hzC : z ∈ f '' C := hCD.symm ▸ hz.1
    obtain ⟨p, hpC, hpz⟩ := hzC
    have hpU : p ∈ U := by
      by_contra hout
      exact hz.2 ⟨p, ⟨hpC, hout⟩, hpz⟩
    have hpx : p = x := mem_singleton_iff.mp (hCU ▸ (show p ∈ C ∩ U from ⟨hpC, hpU⟩))
    simpa [hpx] using hpz.symm
  have hyx : y = f x := huniq y ⟨hyD, hyout⟩
  refine ⟨f x, hyx ▸ hyD, V, hV, ?_⟩
  apply Subset.antisymm
  · intro z hz
    exact mem_singleton_iff.mpr (huniq z hz)
  · rintro z rfl
    exact hyx ▸ (show y ∈ D ∩ V from ⟨hyD, hyout⟩)

/-- A continuous surjective image of a compact scattered space is scattered. -/
theorem scattered_continuous_surjective_image [CompactSpace K] [T2Space L]
    (hK : IsScattered K) (f : K → L) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsScattered L := by
  intro A hA
  have hArange : closure A ⊆ range f := by rw [hsurj.range_eq]; exact subset_univ _
  obtain ⟨y, hy, V, hV, hclosure⟩ := exists_isolated_point_of_compact_image hK f hf
    (closure A) isClosed_closure (hA.mono subset_closure) hArange
  have hyV : y ∈ V := by
    have hm : y ∈ closure A ∩ V := by rw [hclosure]; exact mem_singleton y
    exact hm.2
  obtain ⟨z, hzV, hzA⟩ := mem_closure_iff.mp hy V hV hyV
  have hzy : z = y := mem_singleton_iff.mp (hclosure ▸
    (show z ∈ closure A ∩ V from ⟨subset_closure hzA, hzV⟩))
  have hyA : y ∈ A := hzy ▸ hzA
  refine ⟨y, hyA, V, hV, ?_⟩
  apply Subset.antisymm
  · exact (inter_subset_inter_left V subset_closure).trans hclosure.subset
  · rintro z rfl
    exact ⟨hyA, hyV⟩

/-- A second-countable scattered space has only countably many points. -/
theorem countable_of_scattered_secondCountable [SecondCountableTopology K]
    (hK : IsScattered K) : Countable K := by
  apply Set.countable_univ_iff.mp
  by_contra hunc
  obtain ⟨D, hD, hne, hsub⟩ :=
    exists_perfect_nonempty_of_isClosed_of_not_countable isClosed_univ hunc
  obtain ⟨x, hx, U, hU, hDU⟩ := hK D hne
  have hxU : x ∈ U := by
    have hm : x ∈ D ∩ U := by rw [hDU]; exact mem_singleton x
    exact hm.2
  obtain ⟨y, hy, hyx⟩ := preperfect_iff_nhds.mp hD.acc x hx U (hU.mem_nhds hxU)
  exact hyx (mem_singleton_iff.mp (hDU ▸ (show y ∈ D ∩ U from ⟨hy.2, hy.1⟩)))

end JLMS
