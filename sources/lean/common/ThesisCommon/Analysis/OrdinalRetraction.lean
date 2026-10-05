import ThesisCommon.Analysis.SequenceSpaces

/-! Every nonempty compact subset of an ordinal space is a continuous retract.
The retraction rounds upward to the next point of the compact set and is
constant at its largest point after that point. -/
noncomputable section
open Set Filter Topology
universe u
namespace ThesisCommon

def ordinalCeiling (A : Set Ordinal.{u}) (x : Ordinal.{u}) : Ordinal.{u} := by
  classical
  exact if (A ∩ Ici x).Nonempty then sInf (A ∩ Ici x) else sSup A

theorem ordinalCeiling_mem {A : Set Ordinal.{u}} (hA : IsCompact A)
    (hne : A.Nonempty) (x : Ordinal.{u}) : ordinalCeiling A x ∈ A := by
  classical
  unfold ordinalCeiling
  split_ifs with h
  · exact (csInf_mem h).1
  · exact hA.sSup_mem hne

theorem ordinalCeiling_eq_of_mem {A : Set Ordinal.{u}} {x : Ordinal.{u}}
    (hx : x ∈ A) : ordinalCeiling A x = x := by
  classical
  have h : (A ∩ Ici x).Nonempty := ⟨x, hx, show x ≤ x from le_rfl⟩
  rw [ordinalCeiling, if_pos h]
  exact le_antisymm (csInf_le' ⟨hx, show x ≤ x from le_rfl⟩) (csInf_mem h).2

theorem ordinalCeiling_le_of_mem {A : Set Ordinal.{u}}
    {x a : Ordinal.{u}} (ha : a ∈ A) (hxa : x ≤ a) :
    ordinalCeiling A x ≤ a := by
  classical
  rw [ordinalCeiling, if_pos ⟨a, ha, hxa⟩]
  exact csInf_le' ⟨ha, hxa⟩

theorem le_ordinalCeiling {A : Set Ordinal.{u}} (hA : IsCompact A)
    (hne : A.Nonempty) {x : Ordinal.{u}} (hx : x ≤ sSup A) :
    x ≤ ordinalCeiling A x := by
  classical
  have h : (A ∩ Ici x).Nonempty := ⟨sSup A, hA.sSup_mem hne, hx⟩
  rw [ordinalCeiling, if_pos h]
  exact (csInf_mem h).2

theorem ordinalCeiling_mono {A : Set Ordinal.{u}} (hA : IsCompact A)
    (hne : A.Nonempty) : Monotone (ordinalCeiling A) := by
  intro x y hxy
  by_cases hy : y ≤ sSup A
  · exact ordinalCeiling_le_of_mem (ordinalCeiling_mem hA hne y)
      (hxy.trans (le_ordinalCeiling hA hne hy))
  · have hempty : ¬ (A ∩ Ici y).Nonempty := by
      rintro ⟨a, ha, hya⟩
      exact hy (hya.trans (le_csSup hA.bddAbove ha))
    have heq : ordinalCeiling A y = sSup A := by
      rw [ordinalCeiling, if_neg hempty]
    rw [heq]
    exact le_csSup hA.bddAbove (ordinalCeiling_mem hA hne x)

theorem ordinalCeiling_continuous {A : Set Ordinal.{u}} (hA : IsCompact A)
    (hne : A.Nonempty) : Continuous (ordinalCeiling A) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_order.2
  constructor
  · intro b hb
    by_cases he : (A ∩ Iic b).Nonempty
    · let a := sSup (A ∩ Iic b)
      have ha : a ∈ A ∩ Iic b := (hA.inter_right isClosed_Iic).sSup_mem he
      have hax : a < x := by
        by_contra! h
        exact hb.not_ge ((ordinalCeiling_le_of_mem ha.1 h).trans ha.2)
      filter_upwards [Ioi_mem_nhds hax] with y hy
      by_contra! h
      have hcy : ordinalCeiling A y ≤ a :=
        le_csSup (hA.inter_right isClosed_Iic).bddAbove
          ⟨ordinalCeiling_mem hA hne y, h⟩
      by_cases hymax : y ≤ sSup A
      · exact hy.not_ge ((le_ordinalCeiling hA hne hymax).trans hcy)
      · have hempty : ¬ (A ∩ Ici y).Nonempty := by
          rintro ⟨z, hz, hyz⟩
          exact hymax (hyz.trans (le_csSup hA.bddAbove hz))
        have hmax : ordinalCeiling A y = sSup A := by
          rw [ordinalCeiling, if_neg hempty]
        exact hb.not_ge ((le_csSup hA.bddAbove (ordinalCeiling_mem hA hne x)).trans
          (hmax ▸ h))
    · filter_upwards [] with y
      by_contra! h
      exact he ⟨ordinalCeiling A y, ordinalCeiling_mem hA hne y, h⟩
  · intro b hb
    have hI : Iic x ∈ 𝓝 x := by
      rw [← Order.Iio_succ]
      exact Iio_mem_nhds (Order.lt_succ x)
    filter_upwards [hI] with y hy
    exact (ordinalCeiling_mono hA hne hy).trans_lt hb

def ordinalCompactRetraction {A : Set Ordinal.{u}} (hA : IsCompact A)
    (hne : A.Nonempty) : C(Ordinal.{u}, A) :=
  ⟨fun x => ⟨ordinalCeiling A x, ordinalCeiling_mem hA hne x⟩,
    (ordinalCeiling_continuous hA hne).subtype_mk _⟩

theorem ordinalCompactRetraction_apply {A : Set Ordinal.{u}} (hA : IsCompact A)
    (hne : A.Nonempty) (a : A) : ordinalCompactRetraction hA hne a = a := by
  apply Subtype.ext
  exact ordinalCeiling_eq_of_mem a.property

end ThesisCommon
