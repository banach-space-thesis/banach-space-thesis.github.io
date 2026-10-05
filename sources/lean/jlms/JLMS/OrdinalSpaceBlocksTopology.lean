import JLMS.OrdinalSpaceSplit
import JLMS.OrdinalHeadProjection
import Mathlib.Topology.Order.Compact

/-!
# The clopen blocks of a continuous ordinal embedding

For a strictly increasing continuous map L : [0,γ] → [0,β], consecutive
values delimit the clopen intervals (Lξ,L(ξ+1)]. Distinct blocks are
disjoint. Every point outside the range of L belongs to one such block.
These are the domains used in Kislyakov's Lemma 3.1.
-/

noncomputable section
namespace JLMS
universe u
variable {γ β : Ordinal.{u}}

def ordinalSpaceBlockLeft (L : C(OrdinalInterval γ, OrdinalInterval β))
    (ξ : Set.Iio γ) : Ordinal.{u} := (L ⟨ξ.val, Ordinal.zero_le _, ξ.prop.le⟩).val

def ordinalSpaceBlockRight (L : C(OrdinalInterval γ, OrdinalInterval β))
    (ξ : Set.Iio γ) : Ordinal.{u} :=
  (L ⟨Order.succ ξ.val, Ordinal.zero_le _, Order.succ_le_of_lt ξ.prop⟩).val

def ordinalSpaceBlockLength (L : C(OrdinalInterval γ, OrdinalInterval β))
    (ξ : Set.Iio γ) : Ordinal.{u} := ordinalSpaceBlockRight L ξ - ordinalSpaceBlockLeft L ξ

def ordinalSpaceBlockSet (L : C(OrdinalInterval γ, OrdinalInterval β))
    (ξ : Set.Iio γ) : Set (OrdinalInterval β) :=
  {x | ordinalSpaceBlockLeft L ξ < x.val ∧ x.val ≤ ordinalSpaceBlockRight L ξ}

theorem ordinalSpaceBlock_left_lt_right (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) (ξ : Set.Iio γ) :
    ordinalSpaceBlockLeft L ξ < ordinalSpaceBlockRight L ξ :=
  hL (Order.lt_succ ξ.val)

theorem ordinalSpaceBlock_isClopen (L : C(OrdinalInterval γ, OrdinalInterval β))
    (ξ : Set.Iio γ) : IsClopen (ordinalSpaceBlockSet L ξ) := by
  have he : ordinalSpaceBlockSet L ξ =
      ordinalHeadSet β (ordinalSpaceBlockRight L ξ) \
        ordinalHeadSet β (ordinalSpaceBlockLeft L ξ) := by
    ext x
    simp only [ordinalSpaceBlockSet, ordinalHeadSet, Set.mem_setOf_eq, Set.mem_diff, not_le]
    exact and_comm
  rw [he]
  exact (ordinalHeadSet_isClopen _ _).diff (ordinalHeadSet_isClopen _ _)

instance ordinalSpaceBlockCompactSpace (L : C(OrdinalInterval γ, OrdinalInterval β))
    (ξ : Set.Iio γ) : CompactSpace (ordinalSpaceBlockSet L ξ) :=
  isCompact_iff_compactSpace.mp (ordinalSpaceBlock_isClopen L ξ).isClosed.isCompact

theorem ordinalSpaceBlock_right_le_left (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) {ξ η : Set.Iio γ} (hξη : ξ < η) :
    ordinalSpaceBlockRight L ξ ≤ ordinalSpaceBlockLeft L η :=
  hL.monotone (Order.succ_le_of_lt (show ξ.val < η.val from hξη))

theorem ordinalSpaceBlocks_pairwiseDisjoint (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) :
    Pairwise (fun ξ η => Disjoint (ordinalSpaceBlockSet L ξ) (ordinalSpaceBlockSet L η)) := by
  intro ξ η hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hne with hξη | hηξ
  · exact (not_lt_of_ge ((ordinalSpaceBlock_right_le_left L hL hξη).trans' hx.2)) hy.1
  · exact (not_lt_of_ge ((ordinalSpaceBlock_right_le_left L hL hηξ).trans' hy.2)) hx.1

theorem ordinalSpaceBlock_range_mem_iff (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) (ξ : Set.Iio γ) (η : OrdinalInterval γ) :
    L η ∈ ordinalSpaceBlockSet L ξ ↔ η.val = Order.succ ξ.val := by
  constructor
  · intro h
    have hleft : ξ.val < η.val := hL.lt_iff_lt.mp h.1
    have hright : η.val ≤ Order.succ ξ.val := hL.le_iff_le.mp h.2
    exact le_antisymm hright (Order.succ_le_of_lt hleft)
  · intro h
    have he : η = ⟨Order.succ ξ.val, Ordinal.zero_le _, Order.succ_le_of_lt ξ.prop⟩ :=
      Subtype.ext h
    rw [he]
    exact ⟨ordinalSpaceBlock_left_lt_right L hL ξ, le_rfl⟩

/-- The initial isolated point is in the range and is kept by the restriction summand. -/
theorem exists_ordinalSpaceBlock_of_not_mem_range
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (x : OrdinalInterval β) (hx : x ∉ Set.range L) :
    ∃ ξ : Set.Iio γ, x ∈ ordinalSpaceBlockSet L ξ := by
  let s : Set (OrdinalInterval γ) := {y | L y ≤ x}
  have hs : IsCompact s := (isClosed_le L.continuous continuous_const).isCompact
  have hsn : s.Nonempty := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩, by
    change L _ ≤ x
    rw [hzero]
    exact x.prop.1⟩
  obtain ⟨y, hy, hymax⟩ := hs.exists_isGreatest hsn
  have hyγ : y.val < γ := by
    by_contra! hγy
    have hey : y = ⟨γ, Ordinal.zero_le _, le_rfl⟩ :=
      Subtype.ext (le_antisymm y.prop.2 hγy)
    have hle : L y ≤ x := hy
    rw [hey, htop] at hle
    have hex : x = ⟨β, Ordinal.zero_le _, le_rfl⟩ :=
      Subtype.ext (le_antisymm x.prop.2 hle)
    exact hx ⟨⟨γ, Ordinal.zero_le _, le_rfl⟩, htop.trans hex.symm⟩
  let ξ : Set.Iio γ := ⟨y.val, hyγ⟩
  refine ⟨ξ, ?_, ?_⟩
  · have hlt : L y < x := lt_of_le_of_ne hy (fun he => hx ⟨y, he⟩)
    exact hlt
  · by_contra! hlt
    let z : OrdinalInterval γ := ⟨Order.succ y.val, Ordinal.zero_le _, Order.succ_le_of_lt hyγ⟩
    have hzs : z ∈ s := hlt.le
    exact (not_le_of_gt (Order.lt_succ y.val)) (hymax hzs)

theorem ordinalSpaceBlock_add_length (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) (ξ : Set.Iio γ)
    (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    (ordinalSpaceBlockLeft L ξ + 1) + ordinalSpaceBlockLength L ξ =
      ordinalSpaceBlockRight L ξ := by
  rw [add_assoc, Ordinal.one_add_of_omega0_le hξ]
  exact Ordinal.add_sub_cancel_of_le (ordinalSpaceBlock_left_lt_right L hL ξ).le

def ordinalSpaceBlockPoint (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) (ξ : Set.Iio γ)
    (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    OrdinalInterval (ordinalSpaceBlockLength L ξ) → ordinalSpaceBlockSet L ξ := fun z =>
  ⟨⟨(ordinalSpaceBlockLeft L ξ + 1) + z.val, Ordinal.zero_le _, by
    have h := add_le_add_left z.prop.2 (ordinalSpaceBlockLeft L ξ + 1)
    rw [ordinalSpaceBlock_add_length L hL ξ hξ] at h
    exact h.trans (L ⟨Order.succ ξ.val, Ordinal.zero_le _, Order.succ_le_of_lt ξ.prop⟩).prop.2⟩,
    (lt_add_one _).trans_le (Ordinal.le_add_right _ _), by
      have h := add_le_add_left z.prop.2 (ordinalSpaceBlockLeft L ξ + 1)
      rwa [ordinalSpaceBlock_add_length L hL ξ hξ] at h⟩

theorem continuous_ordinalSpaceBlockPoint (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) (ξ : Set.Iio γ)
    (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    Continuous (ordinalSpaceBlockPoint L hL ξ hξ) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (Ordinal.isNormal_add_right (ordinalSpaceBlockLeft L ξ + 1)).continuous.comp
    continuous_subtype_val

theorem ordinalSpaceBlockPoint_bijective (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) (ξ : Set.Iio γ)
    (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    Function.Bijective (ordinalSpaceBlockPoint L hL ξ hξ) := by
  constructor
  · intro z w h
    apply Subtype.ext
    exact add_left_cancel (congrArg (fun x : ordinalSpaceBlockSet L ξ => x.val.val) h)
  · intro x
    let z : OrdinalInterval (ordinalSpaceBlockLength L ξ) :=
      ⟨x.val.val - (ordinalSpaceBlockLeft L ξ + 1), Ordinal.zero_le _, by
        apply Ordinal.sub_le.mpr
        rw [ordinalSpaceBlock_add_length L hL ξ hξ]
        exact x.prop.2⟩
    refine ⟨z, Subtype.ext (Subtype.ext ?_)⟩
    exact Ordinal.add_sub_cancel_of_le (Order.add_one_le_iff.mpr x.prop.1)

def ordinalSpaceBlockHomeomorph (L : C(OrdinalInterval γ, OrdinalInterval β))
    (hL : StrictMono L) (ξ : Set.Iio γ)
    (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    OrdinalInterval (ordinalSpaceBlockLength L ξ) ≃ₜ ordinalSpaceBlockSet L ξ :=
  (Equiv.ofBijective _ (ordinalSpaceBlockPoint_bijective L hL ξ hξ)).toHomeomorphOfContinuousClosed
    (continuous_ordinalSpaceBlockPoint L hL ξ hξ)
    (continuous_ordinalSpaceBlockPoint L hL ξ hξ).isClosedMap

@[simp] theorem ordinalSpaceBlockHomeomorph_endpoint
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L) (ξ : Set.Iio γ)
    (hξ : Ordinal.omega0 ≤ ordinalSpaceBlockLength L ξ) :
    (ordinalSpaceBlockHomeomorph L hL ξ hξ
      ⟨ordinalSpaceBlockLength L ξ, Ordinal.zero_le _, le_rfl⟩).val =
        L ⟨Order.succ ξ.val, Ordinal.zero_le _, Order.succ_le_of_lt ξ.prop⟩ :=
  Subtype.ext (ordinalSpaceBlock_add_length L hL ξ hξ)

end JLMS
