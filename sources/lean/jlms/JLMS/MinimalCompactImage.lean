import JLMS.ScatteredTopology
import Mathlib.Order.Zorn

/-!
# Minimal compact sets with a prescribed continuous image

A descending chain of closed sets with the same image has that image also
at its intersection: compactness applies inside each fiber. Zorn's lemma
therefore gives a minimal closed set mapping onto a prescribed closed subset.
This is the irreducible-image argument used to preserve scatteredness under
continuous images of compact spaces, a prerequisite for the Asplund argument.
-/

noncomputable section

open Set

namespace JLMS

variable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]
variable [CompactSpace K] [T2Space L]

theorem exists_minimal_closed_image (f : K → L) (hf : Continuous f)
    (D : Set L) (hD : IsClosed D) (hDrange : D ⊆ range f) :
    ∃ C : Set K, IsClosed C ∧ f '' C = D ∧
      ∀ C' : Set K, C' ⊆ C → IsClosed C' → f '' C' = D → C' = C := by
  let S : Set (Set K) := {C | IsClosed C ∧ f '' C = D}
  have hstart : f ⁻¹' D ∈ S := by
    refine ⟨hD.preimage hf, ?_⟩
    exact image_preimage_eq_iff.mpr hDrange
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ S, ∀ C ∈ c, lb ⊆ C := by
    intro c hc hz hne
    obtain ⟨C₀, hC₀⟩ := hne
    letI : Nonempty ↥c := ⟨⟨C₀, hC₀⟩⟩
    let lb := ⋂ C : ↥c, C.val
    have hclosed : IsClosed lb := isClosed_iInter (fun C => (hc C.property).1)
    have hlower (C : Set K) (hC : C ∈ c) : lb ⊆ C :=
      iInter_subset (fun C : ↥c => C.val) ⟨C, hC⟩
    have himage : f '' lb = D := by
      apply Subset.antisymm
      · exact (image_mono (hlower C₀ hC₀)).trans (hc hC₀).2.subset
      · intro y hy
        let F (C : ↥c) := C.val ∩ f ⁻¹' {y}
        have hFclosed (C : ↥c) : IsClosed (F C) :=
          (hc C.property).1.inter (isClosed_singleton.preimage hf)
        have hFne (C : ↥c) : (F C).Nonempty := by
          have hy' : y ∈ f '' C.val := by rw [(hc C.property).2]; exact hy
          obtain ⟨x, hx, hxy⟩ := hy'
          exact ⟨x, hx, hxy⟩
        have hdir : Directed (· ⊇ ·) F := by
          intro C C'
          obtain h | h := hz.total C.property C'.property
          · exact ⟨C, Subset.rfl, inter_subset_inter_left _ h⟩
          · exact ⟨C', inter_subset_inter_left _ h, Subset.rfl⟩
        obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          F hdir hFne (fun C => (hFclosed C).isCompact) hFclosed
        have hxc : x ∈ lb := mem_iInter.mpr (fun C => (mem_iInter.mp hx C).1)
        have hxy : f x = y := (mem_iInter.mp hx ⟨C₀, hC₀⟩).2
        exact ⟨x, hxc, hxy⟩
    exact ⟨lb, ⟨hclosed, himage⟩, hlower⟩
  obtain ⟨C, hCsub, hC⟩ := zorn_superset_nonempty S hchain (f ⁻¹' D) hstart
  refine ⟨C, hC.prop.1, hC.prop.2, ?_⟩
  intro C' hsub hclosed himage
  exact hC.eq_of_le ⟨hclosed, himage⟩ hsub

end JLMS
