import ThesisCommon.Analysis.ALFragmentStrictContent

/-! An actual isometry of fragment Boolean subalgebras preserves their
unnormalized contents, since content is distance from the bottom element. -/
noncomputable section
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
variable (e : E) [Fact (0 ≤ e)] (f : F) [Fact (0 ≤ f)]

theorem norm_positiveFragmentValue_eq_dist_bot (a : PositiveFragmentAlgebra e) :
    ‖positiveFragmentValue a‖ = dist a ⊥ := by
  change ‖positiveFragmentValue a‖ = dist (positiveFragmentValue a) (positiveFragmentValue ⊥)
  rw [positiveFragmentValue_bot, dist_zero_right]

theorem norm_positiveFragmentValue_eq_of_isometry
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (T : BooleanSubalgebra (PositiveFragmentAlgebra f))
    (φ : S ≃o T) (hφ : Isometry φ) (a : S) :
    ‖positiveFragmentValue (φ a).val‖ = ‖positiveFragmentValue a.val‖ := by
  rw [norm_positiveFragmentValue_eq_dist_bot, norm_positiveFragmentValue_eq_dist_bot]
  have h := hφ.dist_eq a ⊥
  simpa only [map_bot, Subtype.dist_eq, BooleanSubalgebra.val_bot] using h

end ThesisCommon
