import ThesisCommon.Analysis.AtomicDualNorming
import ThesisCommon.Analysis.BanachLattice

/-! If the coordinates of an ell-one dual representation preserve the
actual lattice modulus, countably many of them witness failure of DP.
Existence of such an order-compatible representation is a separate theorem. -/
noncomputable section
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E]

theorem normalizedDualAtom_abs
    (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (h : ∀ i x, dualAtom d i |x| = |dualAtom d i x|) (i : Option I) (x : E) :
    normalizedDualAtom d i |x| = |normalizedDualAtom d i x| := by
  cases i with
  | none => simp [normalizedDualAtom]
  | some i =>
    change (dualAtomScale d)⁻¹ * dualAtom d i |x| =
      |(dualAtomScale d)⁻¹ * dualAtom d i x|
    rw [h,abs_mul,abs_of_pos (inv_pos.mpr (dualAtomScale_pos d))]

theorem not_desiredProperty_of_dual_atoms_abs
    (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (he : ∃ e : ℕ → E →L[ℝ] ℝ, IsNorming e)
    (h : ∀ i x, dualAtom d i |x| = |dualAtom d i x|) : ¬ DesiredProperty E := by
  obtain ⟨e,he⟩ := he
  obtain ⟨q,hq⟩ := exists_norming_dual_atoms d e he
  apply not_desiredProperty_iff.mpr
  exact ⟨fun n => normalizedDualAtom d (q n),hq,
    fun x => ⟨|x|,fun n => normalizedDualAtom_abs d h (q n) x⟩⟩

end ThesisCommon
