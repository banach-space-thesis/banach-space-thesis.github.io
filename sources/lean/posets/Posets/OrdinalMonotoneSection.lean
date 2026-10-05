import JLMS.OrdinalSpaceRetraction

/-! A monotone surjection between compact ordinal intervals has a continuous
strictly increasing section: choose the least point of every fiber. This
applies in particular to ceiling projections of closed ordinal cores. -/

noncomputable section
open Set Topology JLMS
namespace Posets
universe u
variable {α β : Ordinal.{u}}

local instance monotoneSectionIntervalFact (γ : Ordinal.{u}) :
    Fact ((0 : Ordinal.{u}) ≤ γ) := ⟨Ordinal.zero_le _⟩

def ordinalMonotoneSection (f : OrdinalInterval α → OrdinalInterval β)
    (y : OrdinalInterval β) : OrdinalInterval α := sInf {x | f x = y}

theorem ordinalMonotoneSection_spec (f : OrdinalInterval α → OrdinalInterval β)
    (hs : Function.Surjective f) (y : OrdinalInterval β) :
    f (ordinalMonotoneSection f y) = y := csInf_mem (hs y)

theorem ordinalMonotoneSection_le_iff (f : OrdinalInterval α → OrdinalInterval β)
    (hm : Monotone f) (hs : Function.Surjective f)
    (y : OrdinalInterval β) (x : OrdinalInterval α) :
    ordinalMonotoneSection f y ≤ x ↔ y ≤ f x := by
  constructor
  · intro h
    simpa only [ordinalMonotoneSection_spec f hs] using hm h
  · intro h
    by_contra hnot
    have hxy : x < ordinalMonotoneSection f y := lt_of_not_ge hnot
    have hfx : f x ≤ y := by
      simpa only [ordinalMonotoneSection_spec f hs] using hm hxy.le
    have hmem : x ∈ {z | f z = y} := le_antisymm hfx h
    exact hnot (sInf_le hmem)

theorem ordinalMonotoneSection_strictMono (f : OrdinalInterval α → OrdinalInterval β)
    (hm : Monotone f) (hs : Function.Surjective f) :
    StrictMono (ordinalMonotoneSection f) := by
  intro y z hyz
  apply lt_of_not_ge
  intro h
  have hzy := hm h
  rw [ordinalMonotoneSection_spec f hs, ordinalMonotoneSection_spec f hs] at hzy
  exact hyz.not_ge hzy

theorem ordinalMonotoneSection_continuous (f : OrdinalInterval α → OrdinalInterval β)
    (hm : Monotone f) (hs : Function.Surjective f) :
    Continuous (ordinalMonotoneSection f) := by
  rw [OrderTopology.continuous_iff]
  intro x
  constructor
  · have he : ordinalMonotoneSection f ⁻¹' Ioi x = Ioi (f x) := by
      ext y
      change x < ordinalMonotoneSection f y ↔ f x < y
      rw [lt_iff_not_ge, ordinalMonotoneSection_le_iff f hm hs, not_le]
    rw [he]
    exact isOpen_Ioi
  · have he : ordinalMonotoneSection f ⁻¹' Iio x =
        ⋃ z : {z : OrdinalInterval α // z < x}, ordinalHeadSet β (f z.val).val := by
      ext y
      simp only [mem_preimage, mem_Iio, mem_iUnion]
      constructor
      · intro hy
        refine ⟨⟨ordinalMonotoneSection f y, hy⟩, ?_⟩
        change y.val ≤ (f (ordinalMonotoneSection f y)).val
        rw [ordinalMonotoneSection_spec f hs]
      · rintro ⟨z, hz⟩
        exact ((ordinalMonotoneSection_le_iff f hm hs y z.val).mpr hz).trans_lt z.property
    rw [he]
    exact isOpen_iUnion (fun z => (ordinalHeadSet_isClopen β (f z.val).val).isOpen)

def ordinalMonotoneSectionMap (f : OrdinalInterval α → OrdinalInterval β)
    (hm : Monotone f) (hs : Function.Surjective f) :
    C(OrdinalInterval β, OrdinalInterval α) :=
  ⟨ordinalMonotoneSection f, ordinalMonotoneSection_continuous f hm hs⟩

theorem exists_ordinalMonotone_continuous_section
    (f : OrdinalInterval α → OrdinalInterval β)
    (hm : Monotone f) (hs : Function.Surjective f) :
    ∃ g : C(OrdinalInterval β, OrdinalInterval α), StrictMono g ∧
      Function.RightInverse g f :=
  ⟨ordinalMonotoneSectionMap f hm hs, ordinalMonotoneSection_strictMono f hm hs,
    ordinalMonotoneSection_spec f hs⟩

end Posets
