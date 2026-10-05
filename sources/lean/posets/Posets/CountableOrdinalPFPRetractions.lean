import ThesisCommon.Analysis.OrdinalRetraction

/-! Coherent ceiling retractions and the clopen cells of the canonical ordinal
tower. These are topological constructions; no operator preservation property
is included as a hypothesis or built into the definitions. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

theorem ordinalCeiling_comp_of_subset {A B : Set Ordinal.{u}}
    (hA : IsCompact A) (hB : IsCompact B) (hBA : B ⊆ A) (hne : B.Nonempty)
    {x : Ordinal.{u}} (hx : x ≤ sSup B) :
    ordinalCeiling B (ordinalCeiling A x) = ordinalCeiling B x := by
  have hneA : A.Nonempty := hne.mono hBA
  have hsup : sSup B ≤ sSup A :=
    csSup_le hne (fun b hb => le_csSup hA.bddAbove (hBA hb))
  apply le_antisymm
  · apply ordinalCeiling_le_of_mem (ordinalCeiling_mem hB hne x)
    exact ordinalCeiling_le_of_mem (hBA (ordinalCeiling_mem hB hne x))
      (le_ordinalCeiling hB hne hx)
  · exact ordinalCeiling_mono hB hne (le_ordinalCeiling hA hneA (hx.trans hsup))

/-- A cell consists of the points rounded to one specified point of the closed
ordinal level. Restricting the domain to a compact ordinal interval also makes
the cell at the last point compact. -/
def ordinalTowerCell (θ : Ordinal.{u}) (A : Set Ordinal.{u}) (a : Ordinal.{u}) :
    Set (Iic θ) := {x | ordinalCeiling A x = a}

theorem ordinalTowerCell_isClopen (θ : Ordinal.{u}) {A : Set Ordinal.{u}}
    (hA : IsCompact A) (hne : A.Nonempty) (a : A)
    (ha : IsOpen ({a} : Set A)) : IsClopen (ordinalTowerCell θ A a) := by
  let r : C(Iic θ, A) := (ordinalCompactRetraction hA hne).comp
    ⟨Subtype.val, continuous_subtype_val⟩
  have heq : ordinalTowerCell θ A a = r ⁻¹' {a} := by
    ext x
    simp only [ordinalTowerCell, mem_setOf_eq, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  rw [heq]
  exact ⟨isClosed_singleton.preimage r.continuous, ha.preimage r.continuous⟩

theorem ordinalTowerCell_isCompact (θ : Ordinal.{u}) {A : Set Ordinal.{u}}
    (hA : IsCompact A) (hne : A.Nonempty) (a : A)
    (ha : IsOpen ({a} : Set A)) : IsCompact (ordinalTowerCell θ A a) := by
  have hc : IsCompact (Iic θ) := by
    have heq : Icc (0 : Ordinal.{u}) θ = Iic θ := by
      ext x
      simp
    rw [← heq]
    exact isCompact_Icc
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp hc
  exact (ordinalTowerCell_isClopen θ hA hne a ha).isClosed.isCompact

theorem ordinalTowerCell_nested_or_disjoint (θ : Ordinal.{u})
    {A B : Set Ordinal.{u}} (hA : IsCompact A) (hB : IsCompact B)
    (hBA : B ⊆ A) (hθ : θ ∈ B) (a b : Ordinal.{u}) :
    ordinalTowerCell θ A a ⊆ ordinalTowerCell θ B b ∨
      Disjoint (ordinalTowerCell θ A a) (ordinalTowerCell θ B b) := by
  have hne : B.Nonempty := ⟨θ, hθ⟩
  have hc (x : Iic θ) : ordinalCeiling B (ordinalCeiling A x) = ordinalCeiling B x :=
    ordinalCeiling_comp_of_subset hA hB hBA hne
      (x.property.trans (le_csSup hB.bddAbove hθ))
  by_cases hab : ordinalCeiling B a = b
  · left
    intro x hx
    change ordinalCeiling A x = a at hx
    change ordinalCeiling B x = b
    rw [← hc x, hx, hab]
  · right
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    apply hab
    change ordinalCeiling A x = a at hxA
    change ordinalCeiling B x = b at hxB
    rw [← hxA, hc x, hxB]

theorem ordinalTowerCell_laminar {ι : Type*} [LinearOrder ι]
    (θ : Ordinal.{u}) (A : ι → Set Ordinal.{u}) (a : ι → Ordinal.{u})
    (hA : ∀ i, IsCompact (A i)) (hmono : Antitone A) (hθ : ∀ i, θ ∈ A i)
    (i j : ι) :
    ordinalTowerCell θ (A i) (a i) ⊆ ordinalTowerCell θ (A j) (a j) ∨
      ordinalTowerCell θ (A j) (a j) ⊆ ordinalTowerCell θ (A i) (a i) ∨
      Disjoint (ordinalTowerCell θ (A i) (a i)) (ordinalTowerCell θ (A j) (a j)) := by
  rcases le_total i j with hij | hji
  · rcases ordinalTowerCell_nested_or_disjoint θ (hA i) (hA j) (hmono hij)
      (hθ j) (a i) (a j) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases ordinalTowerCell_nested_or_disjoint θ (hA j) (hA i) (hmono hji)
      (hθ i) (a j) (a i) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.symm)

theorem ordinalCeiling_isolated_of_isOpen_Ici {A : Set Ordinal.{u}}
    (hA : IsCompact A) (hne : A.Nonempty) {x : Ordinal.{u}}
    (hx : x ≤ sSup A) (ho : IsOpen (Ici x)) :
    IsOpen ({⟨ordinalCeiling A x, ordinalCeiling_mem hA hne x⟩} : Set A) := by
  have hI : IsOpen (Iic (ordinalCeiling A x)) := by
    rw [← Order.Iio_succ]
    exact isOpen_Iio
  have heq : (Subtype.val : A → Ordinal.{u}) ⁻¹'
      (Ici x ∩ Iic (ordinalCeiling A x)) =
      {⟨ordinalCeiling A x, ordinalCeiling_mem hA hne x⟩} := by
    ext a
    constructor
    · intro ha
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact le_antisymm ha.2 (ordinalCeiling_le_of_mem a.property ha.1)
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      change x ≤ ordinalCeiling A x ∧ ordinalCeiling A x ≤ ordinalCeiling A x
      exact ⟨le_ordinalCeiling hA hne hx, le_rfl⟩
  rw [← heq]
  exact (ho.inter hI).preimage continuous_subtype_val

/-- The ancestor cells through a fixed point increase with the level. -/
theorem ordinalTowerCells_monotone {ι : Type*} [Preorder ι]
    (θ : Ordinal.{u}) (A : ι → Set Ordinal.{u})
    (hA : ∀ i, IsCompact (A i)) (hmono : Antitone A) (hθ : ∀ i, θ ∈ A i)
    (x : Iic θ) :
    Monotone (fun i => ordinalTowerCell θ (A i) (ordinalCeiling (A i) x)) := by
  intro i j hij y hy
  change ordinalCeiling (A i) y = ordinalCeiling (A i) x at hy
  change ordinalCeiling (A j) y = ordinalCeiling (A j) x
  have hc (z : Iic θ) := ordinalCeiling_comp_of_subset (hA i) (hA j) (hmono hij)
    (show (A j).Nonempty from ⟨θ, hθ j⟩)
    (z.property.trans (le_csSup (hA j).bddAbove (hθ j)))
  rw [← hc y, hy, hc x]

end Posets
