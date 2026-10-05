import ThesisCommon.Analysis.ALOperatorDirectedSup
import ThesisCommon.Analysis.ALOperatorLattice
import Mathlib.Order.ConditionallyCompleteLattice.Defs

/-! Dedekind completeness of the constructed operator lattice. Directed
positive suprema suffice: translate by one set member and take the positive
elements lying below every translated upper bound. -/
noncomputable section
open Set
open scoped Classical
namespace ThesisCommon

section Order
variable {A : Type*} [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A]

theorem exists_isLUB_of_positive_directed_suprema
    (h : ∀ s : Set A, s.Nonempty → (∀ x ∈ s, 0 ≤ x) → DirectedOn (· ≤ ·) s →
      BddAbove s → ∃ z, IsLUB s z) {s : Set A} (hs : s.Nonempty) (hbdd : BddAbove s) :
    ∃ z, IsLUB s z := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hbdd
  let c : Set A := {x | 0 ≤ x ∧ ∀ u ∈ upperBounds s, x ≤ u - a}
  have hzero : (0 : A) ∈ c := ⟨le_rfl, fun u hu => sub_nonneg.mpr (hu ha)⟩
  have hdir : DirectedOn (· ≤ ·) c := by
    intro x hx y hy
    exact ⟨x ⊔ y, ⟨hx.1.trans le_sup_left, fun u hu => sup_le (hx.2 u hu) (hy.2 u hu)⟩,
      le_sup_left, le_sup_right⟩
  obtain ⟨z, hz⟩ := h c ⟨0, hzero⟩ (fun _ hx => hx.1) hdir ⟨b - a, fun _ hx => hx.2 b hb⟩
  refine ⟨z + a, ?_, ?_⟩
  · intro x hx
    have hmem : (x - a)⁺ ∈ c := by
      refine ⟨posPart_nonneg _, ?_⟩
      intro u hu
      exact sup_le (sub_le_sub_right (hu hx) a) (sub_nonneg.mpr (hu ha))
    exact sub_le_iff_le_add.mp ((le_posPart (x - a)).trans (hz.1 hmem))
  · intro u hu
    exact le_sub_iff_add_le.mp (hz.2 (fun _ hx => hx.2 u hu))
end Order

open scoped PositiveOperatorOrder
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
variable [IsOrderedAddMonoid F] [IsOrderedModule ℝ F] [HasSolidNorm F]
variable [CompleteSpace F] [OrderClosedTopology F]
variable (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
variable (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)

include hALE hALF in
theorem alOperator_exists_isLUB {s : Set (E →L[ℝ] F)} (hs : s.Nonempty) (hbdd : BddAbove s) :
    ∃ T, IsLUB s T := by
  letI := alOperatorLattice hALE hALF
  apply exists_isLUB_of_positive_directed_suprema ?_ hs hbdd
  intro c hc hpos hdir hbdd
  obtain ⟨R, hR⟩ := hbdd
  exact ⟨operatorDirectedSup hALF hc hpos hdir R (fun _ hT => hR hT),
    operatorDirectedSup_isLUB hALF hc hpos hdir R (fun _ hT => hR hT)⟩

def alOperatorSupSet : SupSet (E →L[ℝ] F) where
  sSup s := if h : s.Nonempty ∧ BddAbove s then
    (alOperator_exists_isLUB hALE hALF h.1 h.2).choose else 0

def alOperatorConditionallyCompleteLattice : ConditionallyCompleteLattice (E →L[ℝ] F) := by
  classical
  letI := alOperatorLattice hALE hALF
  letI := alOperatorSupSet hALE hALF
  apply conditionallyCompleteLatticeOfLatticeOfsSup (E →L[ℝ] F)
  intro s hbdd hs
  change IsLUB s (if h : s.Nonempty ∧ BddAbove s then
    (alOperator_exists_isLUB hALE hALF h.1 h.2).choose else 0)
  rw [dif_pos ⟨hs, hbdd⟩]
  exact (alOperator_exists_isLUB hALE hALF hs hbdd).choose_spec

end ThesisCommon
