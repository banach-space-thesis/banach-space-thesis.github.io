import BanachIsometric.GroupLocalCovering
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

/-! A genuine identity chart for a group homomorphism propagates by
translations. When its actual target group is connected, its open subgroup
image is the whole group, and the homomorphism is an actual covering map. -/

namespace BanachIsometric

open Set Topology

variable {E B : Type*} [Group E] [Group B] [TopologicalSpace E] [TopologicalSpace B]
  [IsTopologicalGroup E] [IsTopologicalGroup B]

theorem isLocalHomeomorph_groupHom_of_identity_chart (p : E →* B)
    (e : OpenPartialHomeomorph E B) (he1 : (1 : E) ∈ e.source) (he : (e : E → B) = p) :
    IsLocalHomeomorph p := by
  intro x
  let c := (Homeomorph.mulLeft x⁻¹).toOpenPartialHomeomorph.trans
    (e.trans (Homeomorph.mulLeft (p x)).toOpenPartialHomeomorph)
  refine ⟨c, ?_, ?_⟩
  · change x ∈ Set.univ ∩ (fun z => x⁻¹ * z) ⁻¹'
      (e.source ∩ e ⁻¹' Set.univ)
    simpa only [mem_inter_iff, mem_univ, mem_preimage, inv_mul_cancel, and_true, true_and] using he1
  · funext z
    change p z = p x * e (x⁻¹ * z)
    rw [he, map_mul, map_inv]
    simp only [mul_inv_cancel_left]

theorem surjective_groupHom_of_identity_chart [PreconnectedSpace B] (p : E →* B)
    (e : OpenPartialHomeomorph E B) (he1 : (1 : E) ∈ e.source) (he : (e : E → B) = p) :
    Function.Surjective p := by
  have hp := isLocalHomeomorph_groupHom_of_identity_chart p e he1 he
  have hopen : IsOpen (p.range : Set B) := by
    simpa only [Set.image_univ] using hp.isOpenMap Set.univ isOpen_univ
  have hclosed : IsClosed (p.range : Set B) := p.range.isClosed_of_isOpen hopen
  have hsub : (Set.univ : Set B) ⊆ p.range :=
    isPreconnected_univ.subset_isClopen ⟨hclosed, hopen⟩
      ⟨1, mem_univ _, ⟨1, p.map_one⟩⟩
  intro b
  exact hsub (mem_univ b)

theorem isCoveringMap_groupHom_of_identity_chart [PreconnectedSpace B] (p : E →* B)
    (e : OpenPartialHomeomorph E B) (he1 : (1 : E) ∈ e.source) (he : (e : E → B) = p) :
    IsCoveringMap p :=
  isCoveringMap_of_surjective_group_localHomeomorph p
    (isLocalHomeomorph_groupHom_of_identity_chart p e he1 he)
    (surjective_groupHom_of_identity_chart p e he1 he)

end BanachIsometric
