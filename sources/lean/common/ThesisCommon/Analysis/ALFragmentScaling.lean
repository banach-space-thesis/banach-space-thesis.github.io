import ThesisCommon.Analysis.ALFragmentHomogeneity
import Mathlib.Order.Hom.Set

/-! Positive scalar multiplication is an actual Boolean order isomorphism
of fragment algebras, scaling their norm metrics by that scalar. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

theorem IsPositiveFragment.smul_pos {x y : E} (h : IsPositiveFragment y x)
    {c : ℝ} (hc : 0 < c) : IsPositiveFragment (c • y) (c • x) := by
  refine ⟨smul_nonneg hc.le h.1, smul_le_smul_of_nonneg_left h.2.1 hc.le, ?_⟩
  rw [← smul_sub]
  have hi := (OrderIso.smulRight hc : E ≃o E).map_inf y (x-y)
  change c • (y ⊓ (x-y)) = c • y ⊓ c • (x-y) at hi
  rw [← hi, h.2.2, smul_zero]

variable (e : E) [Fact (0 ≤ e)] (c : ℝ) (hc : 0 < c) [Fact (0 ≤ c • e)]

def positiveFragmentSmulOrderIso :
    PositiveFragmentAlgebra e ≃o PositiveFragmentAlgebra (c • e) where
  toFun a := positiveFragmentOf ((positiveFragmentValue_isFragment a).smul_pos hc)
  invFun a := positiveFragmentOf (by
    simpa only [inv_smul_smul₀ hc.ne'] using
      (positiveFragmentValue_isFragment a).smul_pos (inv_pos.mpr hc))
  left_inv a := by
    apply positiveFragmentValue_injective e
    simp only [positiveFragmentValue_of, inv_smul_smul₀ hc.ne']
  right_inv a := by
    apply positiveFragmentValue_injective (c • e)
    simp only [positiveFragmentValue_of, smul_inv_smul₀ hc.ne']
  map_rel_iff' := by
    intro a b
    change c • positiveFragmentValue a ≤ c • positiveFragmentValue b ↔
      positiveFragmentValue a ≤ positiveFragmentValue b
    exact smul_le_smul_iff_of_pos_left hc

theorem positiveFragmentValue_smulOrderIso (a : PositiveFragmentAlgebra e) :
    positiveFragmentValue (positiveFragmentSmulOrderIso e c hc a) = c • positiveFragmentValue a := rfl

theorem positiveFragmentValue_smulOrderIso_symm (a : PositiveFragmentAlgebra (c • e)) :
    positiveFragmentValue ((positiveFragmentSmulOrderIso e c hc).symm a) =
      c⁻¹ • positiveFragmentValue a := rfl

theorem norm_positiveFragmentSmulOrderIso (a : PositiveFragmentAlgebra e) :
    ‖positiveFragmentValue (positiveFragmentSmulOrderIso e c hc a)‖ = c * ‖positiveFragmentValue a‖ := by
  rw [positiveFragmentValue_smulOrderIso, norm_smul, Real.norm_eq_abs, abs_of_pos hc]

theorem dist_positiveFragmentSmulOrderIso (a b : PositiveFragmentAlgebra e) :
    dist (positiveFragmentSmulOrderIso e c hc a) (positiveFragmentSmulOrderIso e c hc b) =
      c * dist a b := by
  rw [← (isometry_positiveFragmentValue (c • e)).dist_eq,
    ← (isometry_positiveFragmentValue e).dist_eq,
    positiveFragmentValue_smulOrderIso, positiveFragmentValue_smulOrderIso,
    dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc]

theorem continuous_positiveFragmentSmulOrderIso : Continuous (positiveFragmentSmulOrderIso e c hc) := by
  apply (isometry_positiveFragmentValue (c • e)).isEmbedding.continuous_iff.mpr
  exact continuous_const.smul (isometry_positiveFragmentValue e).continuous

theorem continuous_positiveFragmentSmulOrderIso_symm :
    Continuous (positiveFragmentSmulOrderIso e c hc).symm := by
  apply (isometry_positiveFragmentValue e).isEmbedding.continuous_iff.mpr
  exact continuous_const.smul (isometry_positiveFragmentValue (c • e)).continuous

def positiveFragmentSmulHomeomorph :
    PositiveFragmentAlgebra e ≃ₜ PositiveFragmentAlgebra (c • e) where
  toEquiv := (positiveFragmentSmulOrderIso e c hc).toEquiv
  continuous_toFun := continuous_positiveFragmentSmulOrderIso e c hc
  continuous_invFun := continuous_positiveFragmentSmulOrderIso_symm e c hc

include hc in
theorem topologicalDensity_positiveFragment_smul :
    topologicalDensity (PositiveFragmentAlgebra (c • e)) = topologicalDensity (PositiveFragmentAlgebra e) :=
  (topologicalDensity_eq_of_homeomorph (positiveFragmentSmulHomeomorph e c hc)).symm

end ThesisCommon
