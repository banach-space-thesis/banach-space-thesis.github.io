import ThesisCommon.Analysis.ALFragmentPartialExtension
import ThesisCommon.Analysis.BooleanOneSidedBackAndForth
import ThesisCommon.Analysis.PrincipalDensityTop
import ThesisCommon.Analysis.ALHomogeneousIntersectionMatching

/-! Equally homogeneous positive fragment algebras of equal total mass and
equal infinite density admit an actual isometric Boolean order isomorphism.
The construction includes countable density: every proper stage is then finite.
The one-generator extensions use genuine conditional-mass matching. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon
universe u
variable {E F : Type u} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
  [HasSolidNorm F] [CompleteSpace F] [OrderClosedTopology F]
variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)] (f : F) [Fact (0 ≤ f)]

include hE hF in
theorem exists_isometric_booleanOrderIso_of_homogeneous
    (he : IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra e))
    (hf : IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra f))
    (hmass : ‖e‖ = ‖f‖)
    (hden : topologicalDensity (PositiveFragmentAlgebra e) =
      topologicalDensity (PositiveFragmentAlgebra f))
    (hinfinite : ℵ₀ ≤ topologicalDensity (PositiveFragmentAlgebra e)) :
    ∃ q : PositiveFragmentAlgebra e ≃o PositiveFragmentAlgebra f, Isometry q := by
  apply exists_booleanIsometry_of_oneSided_small_extensions
    (topologicalDensity (PositiveFragmentAlgebra e)) hinfinite rfl hden.symm
  · change dist (0 : E) e = dist (0 : F) f
    simpa only [dist_zero_left] using hmass
  · apply exists_alFragment_partialIsometry_extension_of_matching hE hF e f
    intro S T hS hT hsmall φ hφ a
    apply homogeneous_exists_matching_intersections hE e hF f S hS T hT φ hφ hf
    rwa [principalDensity_top, ← hden]
  · apply exists_alFragment_partialIsometry_extension_of_matching hF hE f e
    intro S T hS hT hsmall φ hφ a
    apply homogeneous_exists_matching_intersections hF f hE e S hS T hT φ hφ he
    rwa [principalDensity_top]

end ThesisCommon
