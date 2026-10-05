import Posets.OrdinalClosedCopyBandCells
import Posets.OrdinalAmbientCoreBands

/-! Transport the selected ordinal-band geometry into the actual ambient
space through its open ordinal block embedding. -/

noncomputable section
open Set Topology
universe u v
namespace Posets
open ThesisCommon

variable {F : Set Ordinal.{u}} {θ a b : Ordinal.{u}}
variable (G : OrdinalBandCoreGeometry F θ a b)
variable {K : Type v} [TopologicalSpace K] [T2Space K]
variable (e : Iic θ → K) (he : IsOpenEmbedding e)

theorem ordinalBandCoreGeometry_cell_subset : G.H ⊆ Iic θ := by
  rw [G.cell_eq]
  exact inter_subset_left

def ordinalBandAmbientSet : Set K := e '' ((Subtype.val : Iic θ → Ordinal.{u}) ⁻¹' G.H)

include he in
omit [T2Space K] in
theorem ordinalBandAmbientSet_isCompact : IsCompact (ordinalBandAmbientSet G e) := by
  have hi : IsCompact (Iic θ) := by
    have hh : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
    rw [← hh]
    exact isCompact_Icc
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp hi
  exact ((G.cell_clopen.isClosed.preimage continuous_subtype_val).isCompact).image he.continuous

include he in
theorem ordinalBandAmbientSet_isClopen : IsClopen (ordinalBandAmbientSet G e) :=
  ⟨(ordinalBandAmbientSet_isCompact G e he).isClosed,
    he.isOpenMap _ (G.cell_clopen.isOpen.preimage continuous_subtype_val)⟩

omit [TopologicalSpace K] [T2Space K] in
theorem ordinalBandAmbientSet_subset_range : ordinalBandAmbientSet G e ⊆ range e :=
  image_subset_range _ _

def ordinalBandAmbientHomeomorph : G.H ≃ₜ ordinalBandAmbientSet G e := by
  letI : CompactSpace G.H := isCompact_iff_compactSpace.mp G.cell_compact
  let f : G.H → ordinalBandAmbientSet G e := fun x =>
    ⟨e ⟨x.val, ordinalBandCoreGeometry_cell_subset G x.property⟩,
      ⟨⟨x.val, ordinalBandCoreGeometry_cell_subset G x.property⟩, x.property, rfl⟩⟩
  have hf : Continuous f :=
    (he.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Iic θ => z.val) (he.injective (congrArg Subtype.val hxy))
  have hfs : Function.Surjective f := by
    rintro ⟨y, z, hz, rfl⟩
    exact ⟨⟨z.val, hz⟩, rfl⟩
  exact (show Continuous (Equiv.ofBijective f ⟨hfi, hfs⟩) from hf).homeoOfEquivCompactToT2

theorem ordinalBandAmbientHomeomorph_apply_val (x : G.H) :
    (ordinalBandAmbientHomeomorph G e he x).val =
      e ⟨x.val, ordinalBandCoreGeometry_cell_subset G x.property⟩ := rfl

theorem ordinalBandAmbientHomeomorph_symm_apply_val (x : ordinalBandAmbientSet G e) :
    e ⟨((ordinalBandAmbientHomeomorph G e he).symm x).val,
      ordinalBandCoreGeometry_cell_subset G ((ordinalBandAmbientHomeomorph G e he).symm x).property⟩ =
      x.val :=
  congrArg Subtype.val ((ordinalBandAmbientHomeomorph G e he).apply_symm_apply x)

def ordinalBandAmbientCoordinate :
    C(ordinalBandAmbientSet G e, (ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ G.H))) :=
  G.p.comp ⟨(ordinalBandAmbientHomeomorph G e he).symm,
    (ordinalBandAmbientHomeomorph G e he).symm.continuous⟩

def ordinalBandAmbientSection :
    C((ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ G.H)), ordinalBandAmbientSet G e) :=
  (⟨ordinalBandAmbientHomeomorph G e he,
    (ordinalBandAmbientHomeomorph G e he).continuous⟩ : C(G.H, ordinalBandAmbientSet G e)).comp G.q

theorem ordinalBandAmbientSection_rightInverse :
    Function.RightInverse (ordinalBandAmbientSection G e he) (ordinalBandAmbientCoordinate G e he) := by
  intro y
  change G.p ((ordinalBandAmbientHomeomorph G e he).symm
    (ordinalBandAmbientHomeomorph G e he (G.q y))) = y
  rw [Homeomorph.symm_apply_apply]
  exact G.section_rightInverse y

theorem ordinalBandAmbientSection_apply_val
    (y : ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ G.H)) :
    (ordinalBandAmbientSection G e he y).val =
      e ⟨(G.q y).val, ordinalBandCoreGeometry_cell_subset G (G.q y).property⟩ := rfl

theorem ordinalBandAmbientSection_core
    (y : ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ G.H)) :
    (ordinalBandAmbientSection G e he y).val ∈
      e '' ((Subtype.val : Iic θ → Ordinal.{u}) ⁻¹' F) :=
  ⟨⟨(G.q y).val, ordinalBandCoreGeometry_cell_subset G (G.q y).property⟩,
    (G.section_core y).1, rfl⟩

theorem ordinalBandAmbientSection_leaf_closure
    (L : Set (Iic θ)) (hF : F ⊆ Subtype.val '' closure L)
    (y : ordinalCeiling (ordinalTowerLevel θ a) '' (F ∩ G.H)) :
    (ordinalBandAmbientSection G e he y).val ∈
      closure (e '' L ∩ ordinalBandAmbientSet G e) := by
  let z : Iic θ := ⟨(G.q y).val, ordinalBandCoreGeometry_cell_subset G (G.q y).property⟩
  have hzL : z ∈ closure L := by
    obtain ⟨w, hw, heq⟩ := hF (G.section_core y).1
    have hz : w = z := Subtype.ext heq
    rwa [hz] at hw
  have hzH : z ∈ (Subtype.val : Iic θ → Ordinal.{u}) ⁻¹' G.H := (G.q y).property
  have hz : z ∈ closure (L ∩ ((Subtype.val : Iic θ → Ordinal.{u}) ⁻¹' G.H)) :=
    (G.cell_clopen.isOpen.preimage continuous_subtype_val).closure_inter ⟨hzL, hzH⟩
  have hmem : e z ∈ closure (e '' (L ∩ ((Subtype.val : Iic θ → Ordinal.{u}) ⁻¹' G.H))) :=
    map_mem_closure he.continuous hz (fun z hz => ⟨z, hz, rfl⟩)
  apply (closure_mono ?_) hmem
  rintro x ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw.1, rfl⟩, ⟨w, hw.2, rfl⟩⟩

end Posets
