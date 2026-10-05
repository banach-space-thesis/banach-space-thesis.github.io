import ThesisCommon.Analysis.SigmaComplexRealOrderedModel
import ThesisCommon.Analysis.DualLatticeComplete

/-! The actual real dual of a Banach lattice admits an ordered ℓ¹ model
whenever its Banach-space structure is isomorphic to ℓ¹. -/
noncomputable section
universe u v
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice
namespace ThesisCommon

theorem exists_ordered_dual_ellOne_of_equiv
    {E : Type u} {I : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
    (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1) :
    ∃ J : Type u, ∃ a : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : J => ℝ) 1,
      ∀ φ : E →L[ℝ] ℝ, 0 ≤ φ ↔ ∀ j, 0 ≤ a φ j :=
  exists_ordered_ellOne_of_conditionallyComplete_equiv d

end ThesisCommon

