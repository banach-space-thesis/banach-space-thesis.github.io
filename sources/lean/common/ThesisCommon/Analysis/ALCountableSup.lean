import ThesisCommon.Analysis.ALOrderCompleteness
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Countable

/-! Countable supremum property of complete AL-lattices. Finite suprema are
shifted into the positive cone, then the directed norm-limit theorem selects
a sequence. The union of its finite witnesses is the desired countable set. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]

theorem al_countable_sup_property
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    {s : Set E} {z : E} (hz : IsLUB s z) :
    ∃ c : Set E, c ⊆ s ∧ c.Countable ∧ IsLUB c z := by
  classical
  by_cases hs : s.Nonempty
  swap
  · exact ⟨s, Subset.rfl, (not_nonempty_iff_eq_empty.mp hs) ▸ countable_empty, hz⟩
  obtain ⟨a, ha⟩ := hs
  let D := {d : Finset E // a ∈ d ∧ (↑d : Set E) ⊆ s}
  let v : D → E := fun d => d.1.sup' ⟨a, d.2.1⟩ id - a
  let d₀ : D := ⟨{a}, by simp, by simpa using ha⟩
  have hpos (d : D) : 0 ≤ v d := sub_nonneg.mpr (Finset.le_sup' id d.2.1)
  have hle (d : D) : v d ≤ z - a := by
    apply sub_le_sub_right
    exact Finset.sup'_le _ _ fun x hx => hz.1 (d.2.2 hx)
  have hdir : DirectedOn (· ≤ ·) (range v) := by
    rintro _ ⟨d, rfl⟩ _ ⟨e, rfl⟩
    let q : D := ⟨d.1 ∪ e.1, Finset.mem_union_left _ d.2.1,
      fun x hx => (Finset.mem_union.mp hx).elim (fun h => d.2.2 h) (fun h => e.2.2 h)⟩
    refine ⟨v q, ⟨q, rfl⟩, ?_, ?_⟩
    · apply sub_le_sub_right
      exact Finset.sup'_mono id Finset.subset_union_left _
    · apply sub_le_sub_right
      exact Finset.sup'_mono id Finset.subset_union_right _
  have hbound : BddAbove (norm '' range v) := by
    refine ⟨‖z - a‖, ?_⟩
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (hpos d), abs_of_nonneg (sub_nonneg.mpr (hz.1 ha))]
    exact hle d
  have hvLUB : IsLUB (range v) (z - a) := by
    refine ⟨by rintro _ ⟨d, rfl⟩; exact hle d, ?_⟩
    intro b hb
    apply sub_le_iff_le_add.mpr
    apply hz.2
    intro x hx
    let d : D := ⟨{x, a}, by simp, by
      intro t ht
      have ht' : t = x ∨ t = a := by simpa using ht
      rcases ht' with rfl | rfl
      · exact hx
      · exact ha⟩
    have hvb := hb (show v d ∈ range v from ⟨d, rfl⟩)
    have hxv : x ≤ d.1.sup' ⟨a, d.2.1⟩ id := Finset.le_sup' id (by simp [d])
    exact hxv.trans (sub_le_iff_le_add.mp hvb)
  obtain ⟨w, hw, u, hu, hulim, _⟩ := al_exists_isLUB_of_directed_norm_bdd hAL
    (show (range v).Nonempty from ⟨v d₀, ⟨d₀, rfl⟩⟩)
    (by rintro _ ⟨d, rfl⟩; exact hpos d) hdir hbound
  have hwz : w = z - a := hw.unique hvLUB
  rw [hwz] at hulim
  choose d hd using hu
  let c : Set E := ⋃ n : ℕ, (↑(d n).1 : Set E)
  have hcs : c ⊆ s := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (d n).2.2 hn
  refine ⟨c, hcs, countable_iUnion (fun n => (d n).1.finite_toSet.countable), ?_⟩
  refine ⟨fun x hx => hz.1 (hcs hx), ?_⟩
  intro b hb
  have hseq : ∀ n, u n ≤ b - a := by
    intro n
    rw [← hd n]
    apply sub_le_sub_right
    apply Finset.sup'_le
    intro x hx
    exact hb (mem_iUnion.mpr ⟨n, hx⟩)
  have h := le_of_tendsto' hulim hseq
  exact (sub_le_sub_iff_right a).mp h

end ThesisCommon
