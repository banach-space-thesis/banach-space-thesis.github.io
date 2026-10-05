import ThesisCommon.Analysis.ALAtomicRepresentation
import ThesisCommon.Analysis.ALSchurAtomicity

/-! An AL-lattice which is Banach-space isomorphic to ell-one admits an
ordered ell-one model. Atomicity is proved from Schur, and the ordered
representation is constructed from normalized atoms. -/
noncomputable section
universe u v
namespace ThesisCommon
variable {E : Type u} {I : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
variable [CompleteSpace E]

theorem exists_ordered_ellOne_of_AL_equiv
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) :
    ∃ J : Type u, ∃ a : E ≃L[ℝ] lp (fun _ : J => ℝ) 1,
      ∀ x : E, 0 ≤ x ↔ ∀ j, 0 ≤ a x j :=
  exists_ordered_ellOne_of_atomic_AL hAL
    (fun _ hx hxne => al_exists_atom_of_equiv_ellOne hAL d hx hxne)

end ThesisCommon
