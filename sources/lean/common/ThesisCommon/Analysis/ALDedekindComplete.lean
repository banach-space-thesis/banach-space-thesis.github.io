import ThesisCommon.Analysis.ALOrderCompleteness
import ThesisCommon.Analysis.ALOperatorOrderComplete

/-! Dedekind completeness of the original complete real AL-lattice,
constructed from its norm and order. The resulting conditional lattice
retains the given binary lattice operations. -/
noncomputable section
open Set
open scoped Classical
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
include hAL

theorem al_exists_isLUB {s : Set E} (hs : s.Nonempty) (hb : BddAbove s) :
    ∃ x, IsLUB s x := by
  apply exists_isLUB_of_positive_directed_suprema ?_ hs hb
  intro c hc hpos hdir hbound
  obtain ⟨b, hb⟩ := hbound
  have hb0 : 0 ≤ b := by obtain ⟨a, ha⟩ := hc; exact (hpos a ha).trans (hb ha)
  have hnorm : BddAbove (norm '' c) := by
    refine ⟨‖b‖, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg (hpos a ha), abs_of_nonneg hb0]
      exact hb ha)
  obtain ⟨x, hx, _⟩ := al_exists_isLUB_of_directed_norm_bdd hAL hc hpos hdir hnorm
  exact ⟨x, hx⟩

def alSupSet : SupSet E where
  sSup s := if h : s.Nonempty ∧ BddAbove s then (al_exists_isLUB hAL h.1 h.2).choose else 0

def alConditionallyCompleteLattice : ConditionallyCompleteLattice E := by
  classical
  letI := alSupSet hAL
  apply conditionallyCompleteLatticeOfLatticeOfsSup E
  intro s hb hs
  change IsLUB s (if h : s.Nonempty ∧ BddAbove s then
    (al_exists_isLUB hAL h.1 h.2).choose else 0)
  rw [dif_pos ⟨hs, hb⟩]
  exact (al_exists_isLUB hAL hs hb).choose_spec

end ThesisCommon
