import Posets.OrdinalClosedCopySeparatedAmbientGeometry
import Posets.ScatteredOperators
import Posets.OrdinalRankUnitOmegaBandParameters
import JLMS.OrdinalSpaceBlocksTopology
import JLMS.OrdinalSpaceRetraction

/-! Checked helpers for transfinite anchored block selection.
The upper tower's selected point is isolated.  A source endpoint that survives
one more derivative cannot belong to that selected ceiling fiber. -/

noncomputable section
open Set Topology Order
universe u v w
namespace Posets
open ThesisCommon

theorem ordinalTowerLevel_endpoint_not_mem_isolated_ceiling_cell
    {θ upper : Ordinal.{u}}
    (hθ : θ ∈ ordinalTowerLevel θ (succ upper))
    (y : ordinalTowerLevel θ upper)
    (hy : IsOpen ({y} : Set (ordinalTowerLevel θ upper))) :
    θ ∉ Iic θ ∩ {x | ordinalCeiling (ordinalTowerLevel θ upper) x = y.val} := by
  let A := ordinalTowerLevel θ upper
  have hA : IsClosed A := (ordinalTowerLevel_isCompact θ upper).isClosed
  have hd : θ ∈ derivedSet A := by
    simpa only [ordinalTowerLevel, ordinalDerived_succ] using hθ
  have hθA : θ ∈ A := (isClosed_iff_derivedSet_subset A).mp hA hd
  have he : derivedSet A = (Subtype.val : A → Ordinal.{u}) ''
      derivedSet (univ : Set A) := by
    have hi : (Subtype.val : A → Ordinal.{u}) '' (univ : Set A) = A := by
      ext x
      simp
    calc
      derivedSet A = derivedSet ((Subtype.val : A → Ordinal.{u}) '' univ) :=
        congrArg derivedSet hi.symm
      _ = _ := derivedSet_image_closedEmbedding hA.isClosedEmbedding_subtypeVal univ
  intro hx
  have hyθ : y.val = θ := by
    change θ ∈ ordinalTowerLevel θ upper at hθA
    simpa only [ordinalCeiling_eq_of_mem hθA] using hx.2.symm
  obtain ⟨z, hz, hzθ⟩ := he ▸ hd
  have hzy : z = y := Subtype.ext (hzθ.trans hyθ.symm)
  subst z
  exact ((not_isOpen_singleton_iff_mem_derivedSet_univ y).mpr hz) hy

theorem ordinalSeparatedBandCoreGeometry_endpoint_not_mem
    {F : Set Ordinal.{u}} {θ upper a b rank : Ordinal.{u}}
    (G : OrdinalSeparatedBandCoreGeometry F θ upper a b)
    (hθ : θ ∈ ordinalTowerLevel θ rank) (hmargin : succ upper ≤ rank) :
    θ ∉ G.H := by
  rw [G.cell_eq]
  exact ordinalTowerLevel_endpoint_not_mem_isolated_ceiling_cell
    (ordinalTowerLevel_antitone θ hmargin hθ) G.upperPoint G.upperIsolated

theorem ordinalSeparatedBandAmbientSet_endpoint_not_mem
    {F : Set Ordinal.{u}} {θ upper a b rank : Ordinal.{u}}
    (G : OrdinalSeparatedBandCoreGeometry F θ upper a b)
    {K : Type v} [TopologicalSpace K] [T2Space K]
    (e : Iic θ → K) (he : Function.Injective e)
    (hθ : θ ∈ ordinalTowerLevel θ rank) (hmargin : succ upper ≤ rank) :
    e ⟨θ, le_refl θ⟩ ∉ ordinalSeparatedBandAmbientSet G e := by
  rintro ⟨x, hx, heq⟩
  have hxθ : x = ⟨θ, le_refl θ⟩ := he heq
  exact ordinalSeparatedBandCoreGeometry_endpoint_not_mem G hθ hmargin
    (by simpa only [hxθ] using hx)

theorem ordinalRankUnitOmegaBandLevels_upper_succ_le_rank
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ) (N m k : ℕ)
    (hm : 0 < m) (hk : k < N) :
    succ (ordinalRankUnitOmegaBandLevels ρ N m (k+1)).val ≤
      ρ * (((N+1)*m : ℕ) : Ordinal) :=
  succ_le_of_lt (ordinalRankUnitOmegaBandLevels_upper_lt ρ hρ N m k hm hk)

/-- A cell inside a genuine consecutive block avoids the entire range of the
normal embedding as soon as it avoids that block's right endpoint. -/
theorem ordinalSpaceBlock_cell_disjoint_range
    {γ β : Ordinal.{u}}
    (L : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hL : StrictMono L)
    (ξ : Iio γ) (H : Set (JLMS.OrdinalInterval β))
    (hH : H ⊆ JLMS.ordinalSpaceBlockSet L ξ)
    (hanchor : L ⟨succ ξ.val, Ordinal.zero_le _, succ_le_of_lt ξ.prop⟩ ∉ H) :
    Disjoint H (range L) := by
  apply disjoint_left.mpr
  rintro x hx ⟨η, rfl⟩
  have hη : η.val = succ ξ.val :=
    (JLMS.ordinalSpaceBlock_range_mem_iff L hL ξ η).mp (hH hx)
  have he : η = ⟨succ ξ.val, Ordinal.zero_le _, succ_le_of_lt ξ.prop⟩ :=
    Subtype.ext hη
  exact hanchor (he ▸ hx)

theorem ordinalSpaceBlock_cells_iUnion_disjoint_range
    {γ β : Ordinal.{u}} {I : Type v}
    (L : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hL : StrictMono L)
    (index : I → Iio γ) (H : I → Set (JLMS.OrdinalInterval β))
    (hH : ∀ i, H i ⊆ JLMS.ordinalSpaceBlockSet L (index i))
    (hanchor : ∀ i,
      L ⟨succ (index i).val, Ordinal.zero_le _, succ_le_of_lt (index i).prop⟩ ∉ H i) :
    Disjoint (⋃ i, H i) (range L) := by
  apply disjoint_left.mpr
  intro x hx hxr
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  exact (disjoint_left.mp
    (ordinalSpaceBlock_cell_disjoint_range L hL (index i) (H i) (hH i) (hanchor i)))
    hxi hxr

theorem ordinalSeparatedBandAmbientSet_disjoint_ordinalSpaceRange
    {F : Set Ordinal.{u}} {θ upper a b rank γ β : Ordinal.{u}}
    (G : OrdinalSeparatedBandCoreGeometry F θ upper a b)
    (L : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hL : StrictMono L)
    (ξ : Iio γ) (e : Iic θ → JLMS.OrdinalInterval β) (he : Function.Injective e)
    (hθ : θ ∈ ordinalTowerLevel θ rank) (hmargin : succ upper ≤ rank)
    (hplace : range e ⊆ JLMS.ordinalSpaceBlockSet L ξ)
    (hendpoint : e ⟨θ, le_refl θ⟩ =
      L ⟨succ ξ.val, Ordinal.zero_le _, succ_le_of_lt ξ.prop⟩) :
    Disjoint (ordinalSeparatedBandAmbientSet G e) (range L) := by
  apply ordinalSpaceBlock_cell_disjoint_range L hL ξ
  · exact (ordinalSeparatedBandAmbientSet_subset_range G e).trans hplace
  · rw [← hendpoint]
    exact ordinalSeparatedBandAmbientSet_endpoint_not_mem G e he hθ hmargin

/-- Literal support containment in anchor-free cells makes restriction to the
normal embedding zero.  This is the fact needed for the projection correction. -/
theorem ordinalSpaceRestriction_eq_zero_of_supported_cells
    {𝕜 : Type w} [RCLike 𝕜] {γ β : Ordinal.{u}} {I : Type v}
    (L : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hL : StrictMono L)
    (index : I → Iio γ) (H : I → Set (JLMS.OrdinalInterval β))
    (hH : ∀ i, H i ⊆ JLMS.ordinalSpaceBlockSet L (index i))
    (hanchor : ∀ i,
      L ⟨succ (index i).val, Ordinal.zero_le _, succ_le_of_lt (index i).prop⟩ ∉ H i)
    (f : JLMS.OrdinalC 𝕜 β) (hf : Function.support f ⊆ ⋃ i, H i) :
    JLMS.ordinalSpaceRestriction L f = 0 := by
  ext η
  change f (L η) = 0
  by_contra hne
  exact (disjoint_left.mp
    (ordinalSpaceBlock_cells_iUnion_disjoint_range L hL index H hH hanchor))
    (hf hne) (mem_range_self η)

theorem ordinalSpaceRestriction_comp_eq_zero_of_supported_cells
    {𝕜 : Type w} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {γ β : Ordinal.{u}} {I : Type v}
    (L : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hL : StrictMono L)
    (index : I → Iio γ) (H : I → Set (JLMS.OrdinalInterval β))
    (hH : ∀ i, H i ⊆ JLMS.ordinalSpaceBlockSet L (index i))
    (hanchor : ∀ i,
      L ⟨succ (index i).val, Ordinal.zero_le _, succ_le_of_lt (index i).prop⟩ ∉ H i)
    (J : E →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (hJ : ∀ x, Function.support (J x) ⊆ ⋃ i, H i) :
    (JLMS.ordinalSpaceRestriction L).comp J = 0 := by
  ext x η
  exact congrArg (fun f : JLMS.OrdinalC 𝕜 γ => f η)
    (ordinalSpaceRestriction_eq_zero_of_supported_cells L hL index H hH hanchor (J x) (hJ x))

theorem ordinalSpaceCeilingProjection_comp_eq_zero_of_supported_cells
    {𝕜 : Type w} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {γ β : Ordinal.{u}} {I : Type v}
    (L : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hL : StrictMono L)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (index : I → Iio γ) (H : I → Set (JLMS.OrdinalInterval β))
    (hH : ∀ i, H i ⊆ JLMS.ordinalSpaceBlockSet L (index i))
    (hanchor : ∀ i,
      L ⟨succ (index i).val, Ordinal.zero_le _, succ_le_of_lt (index i).prop⟩ ∉ H i)
    (J : E →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (hJ : ∀ x, Function.support (J x) ⊆ ⋃ i, H i) :
    ((JLMS.ordinalSpaceCeilingExtension L hL htop).comp
      (JLMS.ordinalSpaceRestriction L)).comp J = 0 := by
  rw [ContinuousLinearMap.comp_assoc,
    ordinalSpaceRestriction_comp_eq_zero_of_supported_cells L hL index H hH hanchor J hJ]
  exact ContinuousLinearMap.comp_zero _

end Posets

