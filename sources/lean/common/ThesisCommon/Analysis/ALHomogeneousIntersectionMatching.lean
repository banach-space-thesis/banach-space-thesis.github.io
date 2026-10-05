import ThesisCommon.Analysis.ALConditionalBudgetTransport
import ThesisCommon.Analysis.ALFragmentExactConditionalDivision

/-! Genuine one-fragment matching over smaller-density closed subalgebras.
The matching element is constructed by transporting conditional mass and
then applying exact conditional division. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
  [HasSolidNorm F] [CompleteSpace F] [OrderClosedTopology F]
variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]
variable (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (f : F) [Fact (0 ≤ f)]

include hE hF in
theorem homogeneous_exists_matching_intersections
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (T : BooleanSubalgebra (PositiveFragmentAlgebra f))
    (hT : IsClosed (T : Set (PositiveFragmentAlgebra f)))
    (φ : S ≃o T)
    (hφ : ∀ s : S, ‖positiveFragmentValue (φ s).val‖ = ‖positiveFragmentValue s.val‖)
    (htop : IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra f))
    (hden : topologicalDensity T < principalDensity (⊤ : PositiveFragmentAlgebra f))
    (a : PositiveFragmentAlgebra e) :
    ∃ b : PositiveFragmentAlgebra f, ∀ s : S,
      ‖positiveFragmentValue ((φ s).val ⊓ b)‖ = ‖positiveFragmentValue (s.val ⊓ a)‖ := by
  obtain ⟨g, hg, hg0, hgb, hcut⟩ :=
    exists_transported_conditional_budget hE e hF f S hS T hT φ hφ a
  obtain ⟨b, _, hb⟩ := homogeneous_exists_exact_conditional_mass hF f htop T hT hden
    ⊤ le_rfl g hg hg0 hgb
  refine ⟨b, fun s => ?_⟩
  calc
    ‖positiveFragmentValue ((φ s).val ⊓ b)‖ =
        ‖alFragmentConditionalMass hF f T (b ⊓ (φ s).val)‖ := by
      rw [norm_alFragmentConditionalMass, inf_comm]
    _ = ‖lpCut (booleanStoneSet (φ s).val) (measurableSet_booleanStoneSet _) g‖ := by
      rw [alFragmentConditionalMass_inf_of_mem hF f T b (φ s).val (φ s).property, hb]
    _ = ‖positiveFragmentValue (a ⊓ s.val)‖ := hcut s
    _ = ‖positiveFragmentValue (s.val ⊓ a)‖ := by rw [inf_comm]

end ThesisCommon
