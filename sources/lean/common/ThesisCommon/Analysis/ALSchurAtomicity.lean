import ThesisCommon.Analysis.DyadicHalving
import ThesisCommon.Analysis.ALFragmentNorm

/-! An AL-lattice isomorphic as a Banach space to ell-one is atomic.
An atomless positive vector would admit equal dyadic fragments, whose
Rademacher sequence contradicts the proved Schur property. -/
noncomputable section
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
  [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ u v : E, 0 ≤ u → 0 ≤ v → ‖u+v‖ = ‖u‖+‖v‖)
variable (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1)
include hAL d

theorem al_noAtoms_eq_zero {x : E} (hx : 0 ≤ x) (hno : NoPositiveAtomsBelow x) : x = 0 := by
  classical
  have hsplits (y : E) : ∃ z : E, (0 ≤ y ∧ y ≤ x) →
      IsPositiveFragment z y ∧ ‖z‖ = ‖y‖ / 2 ∧ ‖y-z‖ = ‖y‖ / 2 := by
    by_cases hy : 0 ≤ y ∧ y ≤ x
    · obtain ⟨z,hz,hn,hr,_,_⟩ := al_exists_half_fragment hAL hy.1 (hno.mono hy.2)
      exact ⟨z, fun _ => ⟨hz,hn,hr⟩⟩
    · exact ⟨0, fun h => False.elim (hy h)⟩
  choose a ha using hsplits
  let split (y : E) (b : Bool) := if b then y - a y else a y
  apply eq_zero_of_dyadic_halving x hx split (d := d)
  · intro y hy hyx b
    have h := ha y ⟨hy,hyx⟩
    cases b
    · exact h.1.1
    · exact sub_nonneg.mpr h.1.2.1
  · intro y hy hyx b
    have h := ha y ⟨hy,hyx⟩
    cases b
    · exact h.1.2.1
    · exact sub_le_self _ h.1.1
  · intro y _ _
    change a y + (y-a y) = y
    abel
  · intro y hy hyx
    exact (ha y ⟨hy,hyx⟩).1.2.2
  · intro y hy hyx b
    have h := ha y ⟨hy,hyx⟩
    cases b
    · exact h.2.1
    · exact h.2.2

/-- Every nonzero positive vector dominates a positive lattice atom. -/
theorem al_exists_atom_of_equiv_ellOne {x : E} (hx : 0 ≤ x) (hxne : x ≠ 0) :
    ∃ a : E, IsPositiveLatticeAtom a ∧ a ≤ x := by
  by_contra h
  have hno : NoPositiveAtomsBelow x := by
    intro a _ hax ha
    exact h ⟨a,ha,hax⟩
  exact hxne (al_noAtoms_eq_zero hAL d hx hno)

end ThesisCommon
